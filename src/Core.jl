export mkTheory, matchType, mergeDicts, extend,
       render, getSig, rewrite, sub, normalize, normalize_rec, apply_rewrite,
       buildTerm, upgrade, degrade

using Formatting: format, printfmt

##############################################################################
function mkTheory(name::String,js::Vector{Judgment})::Theory′
    sorts = Dict(x.sort.op=>x for x in js if x isa SortDecl)
    ops = Dict(x.op=>x for x in js if x isa OpDecl)
    eqs = Set(x for x in js if x isa EqDecl)
    return mkTheory′(Theory(name, sorts,ops,eqs))
end

function mkTheory′(t::Theory)::Theory′
    Theory′(t.name,Dict(k=>upgrade(t,v) for (k,v) in t.sorts),
            Dict(k=>upgrade(t,v) for (k,v) in t.ops),
            Set([upgrade(t,e) for e in t.eqs]))
end
##############################################################################
function upgrade(t::Theory′,x::Any) upgrade(degrade(t),x) end
function upgrade(t::Theory,s::SortDecl)::SortDecl′
    SortDecl′(upgrade(t,s.sort),[upgrade(t,a) for a in s.args],s.desc)
end
function upgrade(t::Theory,s::OpDecl)::OpDecl′
    OpDecl′(s.op,upgrade(t,s.sort),[upgrade(t,a) for a in s.args],s.desc)
end
function upgrade(t::Theory,s::EqDecl)::EqDecl′
    EqDecl′(s.name,upgrade(t,s.t1),upgrade(t,s.t2),s.desc,
            [upgrade(t,v) for v in s.xtra])
end
function upgrade(t::Theory,s::Sort)::Sort′
    Sort′(s.op,[upgrade(t,a) for a in s.args])
end
function upgrade(t::Theory,s::Var)::Var′
    Var′(s.sym,upgrade(t,s.sort), s.sortvar)
end
function upgrade(t::Theory,s::App)::App′
    newargs = [upgrade(t,a) for a in s.args]
    patargs = [upgrade(t,a) for a in t.ops[s.op].args]
    pat = upgrade(t,t.ops[s.op].sort)
    #println("pat = $pat")
    #for a in pat.args println("\n\t$a, $(termsort(a))") end
    @assert length(patargs)==length(newargs) "\n$pat\n$s\n$(s.args)"
    subs = mergeDicts(VarDict′[matchType(a,b) for (a,b) in zip(patargs,newargs)])
    @assert subs isa VarDict subs
    Sort = sub(pat, subs)
    return App′(s.op,Sort,newargs)
end
##############################################################################
function degrade(t::SortDecl′)::SortDecl
    SortDecl(degrade(t.sort),[degrade(a) for a in t.args],t.desc)
end
function degrade(t::OpDecl′)::OpDecl
    OpDecl(t.op, degrade(t.sort),[degrade(a) for a in t.args],t.desc)
end
function degrade(t::EqDecl′)::EqDecl
    EqDecl(t.name, degrade(t.t1), degrade(t.t2),t.desc,[degrade(a) for a in t.xtra])
end
function degrade(t::App′)::App App(t.op, [degrade(a) for a in t.args]) end
function degrade(t::Var′)::Var Var(t.sym,degrade(t.sort)) end
function degrade(t::Sort′)::Sort Sort(t.op, [degrade(a) for a in t.args]) end
function degrade(t::Theory′)::Theory
    Theory(t.name, Dict(k=>degrade(v) for (k,v) in t.sorts),
           Dict(k=>degrade(v) for (k,v) in t.ops),
           Set([degrade(x) for x in t.eqs]))
end
##############################################################################

"""Build a term ground up, annotating applications with their inferred sorts
and applying EQ normalization rules when possible. """
function buildTerm(t::Theory′,x::Term)::Term′
    # println("building term $x")
    if x isa Var res = Var′(x.sym,buildTerm(t,x.sort),x.sortvar)
    else
        builtargs = Term′[buildTerm(t,a) for a in x.args]
        if x isa Sort
            res = Sort′(x.op, builtargs)
        else
            @assert haskey(t.ops,x.op) "$(t.ops)\n\t$(x.op)"
            opdecl = t.ops[x.op]
            opsort = opdecl.sort
            @assert length(opdecl.args) == length(x.args) "$x called w/ wrong # args"
            if isempty(x.args)
                return App′(x.op,opdecl.sort)
            else
                # println("$x\n\tbuiltargs $builtargs")
                subs = mergeDicts(VarDict′[
                    matchType(a, b)
                    for (a,b) in zip(opdecl.args,builtargs)])
                @assert subs isa VarDict "building $x:\n$(subs.message)"
                subsort = sub(opsort, subs)
                res = App′(x.op,subsort,builtargs)
            end
        end
    end
    return normalize(t.eqs, res)
end
##############################################################################


function matchType(pat::Term′,x::Term′)::VarDict′
    # println("matchType pat $pat term $x")

    if pat isa Var′
        init = VarDict(pat => x)
        x′=termsort(x)
        err = "\nVar Bad typematch\npat $pat ($(pat.sort.op))\nx $x ($(x′.op))\n"
        @assert x′.op == pat.sort.op err
        rest = VarDict′[matchType(a,b) for (a,b) in zip(pat.sort.args,x′.args)]
        rest′ = mergeDicts(rest)
        return mergeDicts(init,rest′)
    elseif typeof(pat)!=typeof(x) return Error("Nonmatching types $pat \n\t $x")
    elseif pat.op!=x.op return Error("\nApp/Sort Bad typematch\npat $pat\nx $x\n")
    else

        if isempty(pat.args) return Dict{Var′,Term′}()
        else
            return mergeDicts(VarDict′[matchType(a,b) for (a,b) in zip(pat.args,x.args)])
        end
    end
end
##############################################################################

function mergeDicts(x::VarDict′, y::VarDict′)::VarDict′
    if x isa Error return x
    elseif y isa Error return y
    end
    x_ = convert(VarDict,copy(x))
    for (sym, val) in collect(y)
        if haskey(x_, sym) && x_[sym] != val
            err = "Inconsistent defs for variable $sym: $(x_[sym]) vs $val"
            return Error(err)
        else
            x_[sym] = val
        end
     end
     return x_
 end

 function mergeDicts(xs::Union{Vector{VarDict},Vector{Error},Vector{VarDict′}})::VarDict′
    out = VarDict()
    for x in xs
        out = mergeDicts(out, x)
    end
    return out
end
##############################################################################
function sub(t::Term′,ctx::VarDict′)::Term′
    if t isa Var′
        @assert haskey(ctx,t) "$t not found in $ctx"
        return ctx[t]
    elseif t isa Sort′
        return Sort′(t.op,[sub(a,ctx) for a in t.args])
    else
        return App′(t.op,sub(t.sort,ctx), [sub(a,ctx) for a in t.args])
    end
end
##############################################################################

# normalize_memo = Dict{UInt64,Term′}()

"""Repeatedly apply rewrite rules until convergence."""
function normalize(eqs::Set{EqDecl′}, x::Var′)::Var′
    return Var′(x.sym, normalize(eqs,x.sort),x.sortvar)
end

"""For now, we just consider term equality axioms, otherwise, just use the same
code as for App′ and modify apply_rewrite to handle sorts too."""
function normalize(eqs::Set{EqDecl′}, x::Sort′)::Sort′
    return x
end

"""Only normalize at "top level". Assumption is that subarguments are already
in normal form (relative to EqDecls)"""
function normalize_rec(eqs::Set{EqDecl′}, t::Term′)::Term′
    if t isa Var′ return Var′(t.sym,normalize_rec(eqs, t.sort), t.sortvar)
    elseif t isa Sort′ return replace_args(t, Term′[normalize(eqs,a) for a in t.args])
    else return replace_args(t, Term′[normalize(eqs,a) for a in t.args])
    end
end
function normalize(eqs::Set{EqDecl′}, x::App′)::Term′
    #mem = hash(eqs)+hash(x)
    #if haskey(normalize_memo,mem) return normalize_memo[mem] end
    MAX = 5
    seen = Set{App′}([x])
    for counter in 1:MAX
        #println("Loop iter $counter: \n\tx=$x")
        ret = true
        for rule in eqs
            y = apply_rewrite(x,rule)
            # println("\n $(rule.name): $x \n\t→ $y")
            if !(y in seen)
                seen = union(seen,[y])

                # Now, y's subterms may not be normal....do we really have to recurse the whole tree?
                y = normalize_rec(eqs, y)
                seen = union(seen,[y])
                x = y
                ret = false
                break
            end
        end
        if ret return x # normalize_memo[mem]=x
        end # applying all rules did not give us anything new
    end
    @assert false "Counter exceeded: $(t.name), term: $x"
end


"""Try to apply a rewrite rule, if applicable.
Will require slight modification if we have Sort Equalities"""
function apply_rewrite(x::Var′, eq:: EqDecl′)::Var′
    return Var′(x.sym, apply_rewrite(x.sort,eq), x.sortvar)
end
function apply_rewrite(x::Sort′, eq:: EqDecl′)::Sort′
    return Sort′(x.op, Term′[apply_rewrite(a,eq) for a in x.args])
end

function apply_rewrite(x::App′, eq:: EqDecl′, force:: Bool)::Term′
    match = matchType(eq.t2, x)
    if force
        @assert match isa VarDict print(match.message)
    end
    return match isa Error ? x : sub(eq.t1, match)
end
function apply_rewrite(x::App′, eq:: EqDecl′)::Term′ apply_rewrite(x,eq,false) end

##############################################################################

function extend(x::Theory′, y::Theory′,name::String)::Theory′
    extend(x,judgments(degrade(y)),name)
end
function extend(x::Theory′, y::Theory′)::Theory′
    extend(x,judgments(degrade(y)),nothing)
end
function extend(x::Theory′, y::Vector{Judgment}, name::Union{String, Nothing})::Theory′
    js = unique(vcat(judgments(degrade(x)),y))
    newname = name == nothing ? "$(x.name)_$(y.name)" : name
    return mkTheory(newname, js)
end

##############################################################################
function freevars(x::Sort′)::Set{Var′}
    return isempty(x.args) ? Set{Var}() : union([freevars(a) for a in x.args]...)
end
function freevars(x::App′)::Set{Var′}
    return isempty(x.args) ? Set{Var}() : union([freevars(a) for a in x.args]...)
end
function freevars(x::Var′)::Set{Var′}
    if isempty(x.sort.args) return Set([x])
    else return union(Set([x]),[freevars(a) for a in x.sort.args]...)
    end
end
##############################################################################
function getSig(x::SortDecl′)::Premises
    free = isempty(x.args) ? Set() : union([freevars(a) for a in x.args]...)
    return Premises(OrderedDict{Symbol, Sort′}(a.sym => a.sort for a in free))
end
function getSig(x::OpDecl′)::Premises
    sort = freevars(x.sort)
    free = isempty(x.args) ? sort : union(sort,[freevars(a) for a in x.args]...)
    return Premises(OrderedDict{Symbol, Sort′}(a.sym => a.sort for a in free))
end
function getSig(x::EqDecl′)::Premises
    xtra = isempty(x.xtra) ? Set() : union([freevars(a) for a in x.xtra]...)
    free = union(freevars(x.t1),freevars(x.t2),xtra)
    return Premises(OrderedDict{Symbol, Sort′}(a.sym => a.sort for a in free))
end
##############################################################################
function render(t::Theory′,x::T)::String where {T<:Union{Var,Var′,Op}}
    string(x.sym)
end
function render(t::Theory′,x::T)::String where {T<:Union{Sort,Sort′,App,App′}}
    format(x.op.pat, [render(t,z) for z in x.args]...)
end


function render(t::Theory′, x::SortDecl′)::String
    top = render(t, getSig(x))
    if isempty(x.args)
        bot = string(x.sort.op.pat)
    else
        bot = format(x.sort.op.pat, [render(t,q) for q in x.args]...)
    end

    return printRule(top, string(bot, "  sort"), string(x.sort.op.sym),x.desc)
end
function render(t::Theory′, x::Premises)::String
    sorts = sort(unique(collect(values(x.premises))))
    dic = Dict([join([string(k) for (k,v) in sort(x.premises) if v==s],",")=>render(t,s) for s in sorts])
    return join([string(k,":",v) for (k,v) in dic], "  ")
end
function render(t::Theory′,  x::OpDecl′)::String
    top = render(t, getSig(x))
    sor = render(t,x.sort)
    bot = string(format(x.op.pat, [render(t,z) for z in x.args]...), " : ", sor)
    return printRule(top, bot, string(x.op.sym),x.desc)
end

function render(t::Theory′, x::EqDecl′)::String
    top = render(t, getSig(x))
    bot = format("{} = {} : {}", render(t, x.t1), render(t, x.t2),
                 render(t, termsort(x.t1)))
    return  printRule(top, bot, x.name, x.desc)
end

function render(x::Theory′)::String
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
##############################################################################
function replace_args(x::T,args::Vector{Term′})::T where{T <: Term′}
    if x isa Var′ return x
    elseif x isa Sort′ return Sort′(x.op, args)
    else return App′(x.op, x.sort, args)
    end
end
