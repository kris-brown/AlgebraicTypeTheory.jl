export SortOp, TermOp, App, Sort, Term, Var, EqDecl, Premises, Judgment, Theory,
       mkTheory, infer,infertemplate,matchType,mergeDicts, validate, extend,
       render, getSig
using Formatting: FormatExpr, format, printfmt
using AutoHashEquals: @auto_hash_equals
using DataStructures: OrderedDict

abstract type Term end
abstract type Op end

# Two types of operators, sort constructors and term-constructors
@auto_hash_equals struct SortOp <: Op
    sym :: Symbol
    pat :: String
    SortOp(sym,pat) = pat=="binary" ? new(sym,string("({} ",sym," {})")) : new(sym,pat)

end

@auto_hash_equals struct TermOp <: Op
    sym :: Symbol
    pat :: String
    TermOp(sym,pat) = pat=="binary" ? new(sym,string("({} ",sym," {})")) : new(sym,pat)
end

function arity(op::T)::Int where {T<:Op} length(FormatExpr(op.pat).entries) end

SortOp(sym::Symbol, arity::Int) = (SortOp(sym,arity==0 ? string(sym)
    : string(sym,"(",join(repeat(["{}"],arity),","),")")))
SortOp(sym::Symbol) = SortOp(sym, 0)
TermOp(sym::Symbol, arity::Int) = TermOp(sym,arity==0 ? string(sym) : string(sym,"(",join(repeat(["{}"],arity),","),")"))
TermOp(sym::Symbol) = TermOp(sym, 0)

# Three types of terms, Variables, Applications, and Sorts
""" Result of application of term operation"""
@auto_hash_equals struct App <: Term
    op::TermOp
    args::Vector{Term}
    function App(op:: TermOp,args :: Vector{T}) where {T<:Term}
        err = "Incorect # of args\n$op\n$(op.pat)\n$(args)"
        @assert arity(op) == length(args) err
        new(op,args)
    end
end

App(op::TermOp)=App(op,Term[])

"""Datatype for CLOSED sorts. Sorts themselves can be terms.
A sort has a sort constructor and some arguments that can be used together to
infer what the sort is."""
@auto_hash_equals struct Sort <: Term
    op::SortOp
    args::Vector{Term}
    function Sort(op:: SortOp,args :: Vector{T}) where {T<:Term}
        err = "Incorect # of args\n$op\n$(op.pat)\n$(args)"
        @assert arity(op) == length(args) err
        new(op,args)
    end
end

Sort(op::SortOp)=Sort(op,Term[])

"""Unknown value of some sort."""
@auto_hash_equals struct Var <: Term
    sym::Symbol
    sort::Sort
end


"""Declare a new sort w/r/t prototypical arguments, whose variable
names may be subtituted for a concrete sort."""
@auto_hash_equals struct SortDecl
    sort :: Sort
    args :: Vector{Term}
    desc :: String
    function SortDecl(sort:: Sort,args :: Vector{T},desc :: String) where {T<:Term}
        @assert arity(sort.op) == length(args) "Incorect # of args\n$sort\n$(sort.op.pat)\n$(args)"
        new(sort,args,desc)
    end

end
SortDecl(s::Sort)=SortDecl(s,Term[],"")
SortDecl(s::Sort,desc::String)=SortDecl(s,Term[],desc)
SortDecl(s::Sort,args::Vector{T}) where {T<:Term} = SortDecl(s,args,"")

"""Declare relationship between output sort of an application w/r/t prototypical
arguments.

The sort field CAN be a general term (rather than restricted to just a Sort)
because it is possible for a Sort Equality declaration to say that certain
elements are sorts, e.g. top of page 17 of ATT&GC.

"""
@auto_hash_equals struct OpDecl
    op:: TermOp
    sort::Term
    args :: Vector{Term}
    desc :: String
    function OpDecl(op:: TermOp, sort::Term, args :: Vector{T},desc::String) where {T<:Term}
        @assert arity(op) == length(args) "Incorect # of args\n$op\n$(op.pat)\n$(args)"
        new(op, sort, args, desc)
    end
end
OpDecl(op::TermOp,s::Term)=OpDecl(op,s,Term[],"")
OpDecl(op::TermOp,s::Term,desc::String)=OpDecl(op,s,Term[],desc)
OpDecl(op::TermOp,s::Term,args::Vector{T}) where {T<:Term} = OpDecl(op,s,args,"")

@auto_hash_equals struct EqDecl
    name:: String
    t1::Term
    t2::Term
    desc::String
    xtra::Vector{Var}  # extra assumptions not included in terms
end
EqDecl(name:: String,t1::Term,t2::Term) = EqDecl(name,t1,t2,"",Var[])
EqDecl(name:: String,t1::Term,t2::Term, desc::String) = EqDecl(name,t1,t2,desc,Var[])

@auto_hash_equals struct Premises
    premises::OrderedDict{Symbol,Sort}
end

@auto_hash_equals struct Theory
    name :: String
    sorts :: Dict{SortOp,SortDecl}
    ops :: Dict{TermOp, OpDecl}
    eqs :: Set{EqDecl}
end

Judgment = Union{SortDecl,OpDecl,EqDecl}
function mkTheory(name::String,js::Vector{Judgment}, val::Bool)::Theory
    sorts = Dict(x.sort.op=>x for x in js if x isa SortDecl)
    ops = Dict(x.op=>x for x in js if x isa OpDecl)
    eqs = Set(x for x in js if x isa EqDecl)
    t = Theory(name, sorts,ops,eqs)
    if val validate(t) end
    return t
end

"""Validate by default"""
function mkTheory(n::String,js::Vector{Judgment})::Theory mkTheory(n, js, true) end

"""By default, we don't validate things that aren't given a name"""
function mkTheory(js::Vector{Judgment})::Theory mkTheory("theory", js, false) end
##############################################################################
"""Since some terms can be declared sorts via Sort Equality, sort inference can
return a general Term."""
function infer(t::Theory,x::Term)::Term
    if x isa Var return x.sort
    elseif x isa Sort
        @assert haskey(t.sorts,x.op)
        temp = t.sorts[x.op]
    elseif x isa App
        @assert haskey(t.ops,x.op)
        temp = t.ops[x.op]
    else throw(DomainError)
    end
    err = "Wrong # of args: temp $temp\n x $x"
    @assert length(temp.args) == length(x.args) err
    return infertemplate(t, temp.sort, temp.args, x)
end

"""Given a pattern template w/r/t prototypical arguments, use some particular
arguments to instantiate a sort with the same structure as the pattern."""
function infertemplate(t::Theory,temp::Term,targs::Vector{Term},
                       x::Union{App,Sort})::Term
    #println("InferTemplate temp \n$temp\n\ntargs $targs\n\nterm $x\n\n")
    if isempty(targs) return temp end
    subs = mergeDicts([matchType(t,a,b) for (a,b) in zip(targs,x.args)])
    return sub(temp, subs)
end

"""
Modify varname with a hash to identify which application/sort it comes from
"""
function encodeVar(t::Term,v::Var)::Var
    return Var(Symbol(string(hash(t),v.sym)), v.sort)
end

function matchType(t::Theory, pat::T,x::U)::Dict{Var,Term} where {T<:Term,U<:Term}
    if pat isa Var
        return mergeDicts(Dict(pat=>x),matchType(t,pat.sort,infer(t,x)))
    elseif (pat isa Sort && x isa Var) x = x.sort
    elseif (pat isa Sort && x isa App) x = infer(t,x)
    end
    err = "matchType pat $pat\nterm $x"
    @assert typeof(pat) == typeof(x) err
    #println("MatchType pat $pat\nterm $x")
    @assert pat.op==x.op "\nBad typematch\npat $pat\nx $x\n"
    if isempty(pat.args) return Dict{Var,Term}()
    else return mergeDicts([matchType(t,a,b) for (a,b) in zip(pat.args,x.args)])
    end
end
##############################################################################
function mergeDicts(x::Dict{Var, T}, y::Dict{Var, U}
                    )::Dict{Var, Term} where {T<:Term,U<:Term}
    x_ = convert(Dict{Var, Term},copy(x))
    for (sym, val) in collect(y)
        if haskey(x_, sym)
            err = "Inconsistent defs for variable $sym: $(x_[sym]) vs $val"
            @assert x_[sym] == val err
        else
            x_[sym] = val
        end
     end
     return sort(x_)
 end

 function mergeDicts(xs::Vector{Dict{Var, T}})::Dict{Var, Term} where {T<:Term}
    out = Dict{Var, Term}()
    for x in xs
        out = mergeDicts(out, x)
    end
    return sort(out)
end
##############################################################################
function sub(t::Term,ctx::Dict{Var,Term})::Term
    if t isa Var
        @assert haskey(ctx,t) "$t not found in $ctx"
        return ctx[t]
    elseif t isa Sort return Sort(t.op,[sub(a,ctx) for a in t.args])
    else              return App(t.op,[sub(a,ctx) for a in t.args])
    end
end
##############################################################################
function validate(t::Theory)::Nothing
    [validate(t,v) for x in [t.sorts,t.ops] for v in collect(values(x)) ]
    [validate(t,a) for a in t.eqs]
    return nothing
end
function validate(t::Theory,s::SortDecl)::Nothing
    #println(s)
    [validate(t, sv) for sv in s.args]
    validate(t,s.sort)
end
function validate(t::Theory,s::OpDecl)::Nothing
    #println(s)
    [validate(t, sv) for sv in s.args]
    validate(t,s.sort)
end
function validate(t::Theory,s::EqDecl)::Nothing
    # println(s)
    s1,s2 = [infer(t,s.t1), infer(t,s.t2)]
    @assert s1 == s2 "$(s.name) has t1 $(s.t1)\n\t$s1\n\nt2 $(s.t2)\n\t$s2"
    validate(t,s.t1)
    validate(t,s.t2)
end
function validate(t::Theory,s::Var)::Nothing
    validate(t,s.sort)
end
function validate(t::Theory,s::Sort)::Nothing
    err = "Sort Expression is not found in the theory ($(keys(t.sorts)))"
    #[validate(t,a) for a in s.args]
    @assert haskey(t.sorts, s.op) err
    infer(t,s)
    return nothing
end
function validate(t::Theory,s::App)::Nothing
    err = "Sort Expression is not found in the theory ($(keys(t.sorts)))"
    #[validate(t,a) for a in s.args]
    @assert haskey(t.ops, s.op) err
    infer(t,s)
    return nothing
end
##############################################################################
function extend(x::Theory, y::Theory,name::String)::Theory
    extend(x,y,name, true)
end
function extend(x::Theory, y::Theory)::Theory
    extend(x,y,nothing, false)
end
function extend(x::Theory, y::Theory, name::Union{String, Nothing},
                validate::Bool)::Theory
    # Check that there are no conflicting definitions of sorts
    for (k,v) in collect(y.sorts)
        if haskey(x.sorts,k)
            @assert x.sorts[k] == y.sorts[k]
        end
    end
    sorts = vcat(collect(values(x.sorts)), collect(values(y.sorts)))

    # same for ops
    for (k,v) in collect(y.ops)
        if haskey(x.ops,k)
            @assert x.ops[k] == y.ops[k] "$(x.ops[k]) != $(y.ops[k])"
        end
    end
    ops = vcat(collect(values(x.ops)), collect(values(y.ops)))

    # union of equality constraints
    eqs = vcat(collect(x.eqs), collect(y.eqs))

    # Combine everything and make unique
    out = map(z->convert(Vector{Judgment}, unique(z)),
              [sorts, ops, eqs])

    newname = name == nothing ? "$(x.name)_$(y.name)" : name
    return mkTheory(newname, vcat(collect(out)...), validate)
end


function freevars(x::Sort)::Set{Var}
    return isempty(x.args) ? Set{Var}() : union([freevars(a) for a in x.args]...)
end
function freevars(x::App)::Set{Var}
    return isempty(x.args) ? Set{Var}() : union([freevars(a) for a in x.args]...)
end
function freevars(x::Var)::Set{Var}
    if isempty(x.sort.args) return Set([x])
    else return union(Set([x]),[freevars(a) for a in x.sort.args]...)
    end
end

function getSig(x::SortDecl)::Premises
    free = isempty(x.args) ? Set() : union([freevars(a) for a in x.args]...)
    return Premises(OrderedDict{Symbol, Sort}(a.sym => a.sort for a in free))
end
function getSig(x::OpDecl)::Premises
    free = isempty(x.args) ? Set() : union([freevars(a) for a in x.args]...)
    return Premises(OrderedDict{Symbol, Sort}(a.sym => a.sort for a in free))
end
function getSig(x::EqDecl)::Premises
    xtra = isempty(x.xtra) ? Set() : union([freevars(a) for a in x.xtra]...)
    free = union(freevars(x.t1),freevars(x.t2),xtra)
    return Premises(OrderedDict{Symbol, Sort}(a.sym => a.sort for a in free))
end
##############################################################################
function render(t::Theory,x::Var)::String string(x.sym) end
function render(t::Theory,x::Op)::String string(x.sym) end
function render(t::Theory,x::Sort)::String
    format(x.op.pat, map(z->render(t,z),x.args)...)
end
function render(t::Theory,x::App)::String
    format(x.op.pat, map(z->render(t,z),x.args)...)
end


function render(t::Theory, x::SortDecl)::String
    top = join(map(((k, v),)-> string(k,":", render(t,v)),
                   sort(collect(getSig(x)))), "  ")
    if isempty(x.args)
        bot = string(x.sort.op.pat)
    else
        bot = format(x.sort.op.pat, map(q->render(t,q),x.args)...)
    end

    return printRule(top, string(bot, "  sort"), string(x.sort.op.sym),x.desc)
end

function render(t::Theory,  x::OpDecl)::String
    top = join(map(((k, v),)-> string(k,":", render(t,v)),
                   sort(collect(getSig(x)))), " ")
    sor = render(t,x.sort)
    bot = string(format(x.op.pat, map(z->render(t,z),x.args)...), " : ", sor)
    return printRule(top, bot, string(x.op.sym),x.desc)
end

function render(t::Theory, x::EqDecl)::String
    top = join(map(((k,v),)-> string(k,":", render(t,v)),
                   sort(collect(getSig(x)))), "  ")
    bot = format("{} = {} : {}", render(t, x.t1), render(t, x.t2),
                 render(t, infer(t,x.t1)))
    return  printRule(top, bot, x.name, x.desc)
end

function render(x::Theory)::String
    function box(s::String)::Vector{String}
        line = '#'^(length(s)+4)
        return [join([line,string("# ",s," #"),line], "\n")]
    end
    judgments = vcat("",box("******* Theory: $(x.name) *******"), box("Sorts"),
                     [render(x,z) for z in sort(collect(values(x.sorts)))]...,
                     box("Operations"),
                     [render(x,z) for z in sort(collect(values(x.ops)))]...,
                     box("Equality Axioms"),
                     [render(x,z) for z in sort(collect(x.eqs))]...)
    return(join(judgments, "\n\n"))
end

##############################################################################
function printRule(top::String, bot::String, name::String, desc::String)::String
    lt, lb = map(length, [top, bot])
    line = '-'^max(lt, lb)
    offt = ' '^((length(line)-lt)÷2)
    offb = ' '^((length(line)-lb)÷2)
    out = join(["***",string(offt, top),"$line   $name",string(offb, bot),
                isempty(desc) ? "" : "\n$desc\n"], '\n')
    return out
end

function Base.show(io::IO,x::SortOp) print(io,x.sym) end
function Base.show(io::IO,x::TermOp) print(io,x.sym) end
function Base.show(io::IO,x::Var) printfmt(io, "({}::{})",x.sym,x.sort) end
function Base.show(io::IO,x::App) printfmt(io,x.op.pat,x.args...) end
function Base.show(io::IO,x::Sort) printfmt(io,x.op.pat,x.args...) end
function Base.show(io::IO,x::SortDecl)
    printfmt(io,"DECL {}({}) :: {}",x.sort.op,join(x.args,","),x.sort)
end
function Base.show(io::IO,x::OpDecl)
    printfmt(io,string("DECL ",x.op.pat," :: {}"),x.args...,x.sort)
end
function Base.show(io::IO,x::EqDecl)
    printfmt(io,string("EQ ",x.name,"\n\t{} = {}"),x.t1, x.t2)
end
function Base.show(io::IO,t::Theory)
    println(string(t.name,"\n\n*Sorts*\n"))
    println(io, join(collect(values(t.sorts)),"\n\n"))
    println("\n\n*Operators*\n")
    println(io, join(collect(values(t.ops)),"\n\n"))
    println("\n\n*Axioms*\n")
    println(io, join(collect(t.eqs),"\n\n"))
end

function Base.isless(x::Op, y::Op)::Bool x.sym < y.sym end
function Base.isless(x::Term, y::Term)::Bool hash(x) < hash(y) end
function Base.isless(x::SortDecl, y::SortDecl)::Bool hash(x) < hash(y) end
function Base.isless(x::OpDecl, y::OpDecl)::Bool  hash(x) < hash(y) end
function Base.isless(x::EqDecl, y::EqDecl)::Bool  hash(x) < hash(y) end
function Base.length(x::Premises) length(x.premises) end
function Base.iterate(x::Premises) iterate(x.premises) end
function Base.iterate(x::Premises,i::Int) iterate(x.premises,i) end
