module DataTypes
export SortOp, TermOp, App, Sort, Term, Var, SortDecl, OpDecl, EqDecl, Premises,
       Judgment, Theory, App′, Sort′, Term′, Var′, SortDecl′, OpDecl′, EqDecl′,
       Judgment′, Theory′, termsort, judgments, VarDict, VarDict′
using AutoHashEquals: @auto_hash_equals
using DataStructures: OrderedDict
using Formatting: FormatExpr, printfmt

##############################################################################
abstract type Term end
abstract type Term′ end
abstract type Op end

##############################################################################
struct Error
    message::String
end

# Two types of operators, sort constructors and term-constructors
@auto_hash_equals struct SortOp <: Op
    sym::Symbol
    pat::String
    SortOp(sym, pat) = pat == "binary" ? new(sym, string("({} ", sym, " {})")) : new(sym, pat)

end

@auto_hash_equals struct TermOp <: Op
    sym::Symbol
    pat::String
    TermOp(sym, pat) = pat == "binary" ? new(sym, string("({} ", sym, " {})")) : new(sym, pat)
end

"""
Arity "{1} {2} {1}" == 2
Arity "{1} {4}" == 4
"""
function arity(op::T)::Int where {T <: Op}
    length(Set(FormatExpr(op.pat).entries))
end

SortOp(sym::Symbol, arity::Int) = (SortOp(sym,arity == 0 ? string(sym)
    : string(sym, "(", join(repeat(["{}"], arity), ","), ")")))
SortOp(sym::Symbol) = SortOp(sym, 0)
TermOp(sym::Symbol, arity::Int) = TermOp(sym, arity == 0 ? string(sym) : string(sym, "(", join(repeat(["{}"], arity), ","), ")"))
TermOp(sym::Symbol) = TermOp(sym, 0)

# Three types of terms, Variables, Applications, and Sorts
""" Result of application of term operation"""
@auto_hash_equals struct App <: Term
    op::TermOp
    args::Vector{Term}
    function App(op::TermOp, args::Vector{T}) where {T <: Term}
        err = "Incorect # of args\n$op\n$(op.pat)\n$(args)"
        @assert arity(op) == length(args) err
        new(op, args)
    end
end

App(op::TermOp) = App(op, Term[])


"""Datatype for CLOSED sorts. Sorts themselves can be terms.
A sort has a sort constructor and some arguments that can be used together to
infer what the sort is."""
@auto_hash_equals struct Sort <: Term
    op::SortOp
    args::Vector{Term}
    function Sort(op::SortOp, args::Vector{T}) where {T <: Term}
        err = "Incorect # of args\n$op\n$(op.pat)\n$(args)"
        @assert arity(op) == length(args) err
        new(op, args)
    end
end

Sort(op::SortOp) = Sort(op, Term[])

"""Unknown value of some sort."""
@auto_hash_equals struct Var <: Term
    sym::Symbol
    sort::Sort
    sortvar::Bool
end

Var(sym::Symbol,sort::Sort) = Var(sym, sort, false)

"""Declare a new sort w/r/t prototypical arguments, whose variable
names may be subtituted for a concrete sort."""
@auto_hash_equals struct SortDecl
    sort::Sort
    args::Vector{Term}
    desc::String
    function SortDecl(sort::Sort, args::Vector{T}, desc::String) where {T <: Term}
        @assert arity(sort.op) == length(args) "Incorect # of args\n$sort\n$(sort.op.pat)\n$(args)"
        new(sort, args, desc)
    end

end
SortDecl(s::Sort) = SortDecl(s, Term[], "")
SortDecl(s::Sort,desc::String) = SortDecl(s, Term[], desc)
SortDecl(s::Sort,args::Vector{T}) where {T <: Term} = SortDecl(s, args, "")

"""Declare relationship between output sort of an application w/r/t prototypical
arguments.

The sort field CAN be a general term (rather than restricted to just a Sort)
because it is possible for a Sort Equality declaration to say that certain
elements are sorts, e.g. top of page 17 of ATT&GC.

"""
@auto_hash_equals struct OpDecl
    op::TermOp
    sort::Sort
    args::Vector{Term}
    desc::String
    function OpDecl(op::TermOp, sort::Term, args::Vector{T}, desc::String) where {T <: Term}
        @assert arity(op) == length(args) "Incorect # of args\n$op\n$(op.pat)\n$(args)"
        new(op, sort, args, desc)
    end
end
OpDecl(op::TermOp,s::Term) = OpDecl(op, s, Term[], "")
OpDecl(op::TermOp,s::Term,desc::String) = OpDecl(op, s, Term[], desc)
OpDecl(op::TermOp,s::Term,args::Vector{T}) where {T <: Term} = OpDecl(op, s, args, "")

@auto_hash_equals struct EqDecl
    name::String
    t1::Term
    t2::Term
    desc::String
    xtra::Vector{Var}  # extra assumptions not included in terms
end
EqDecl(name::String,t1::Term,t2::Term) = EqDecl(name, t1, t2, "", Var[])
EqDecl(name::String,t1::Term,t2::Term, desc::String) = EqDecl(name, t1, t2, desc, Var[])

@auto_hash_equals struct Theory
    name::String
    sorts::Dict{SortOp,SortDecl}
    ops::Dict{TermOp,OpDecl}
    eqs::Set{EqDecl}
end

Judgment = Union{SortDecl,OpDecl,EqDecl}
function judgments(t::Theory)::Vector{Judgment}
    [values(t.sorts)...,values(t.ops)...,t.eqs...]
end
##############################################################################
# Enriched data structures #
############################
@auto_hash_equals struct Sort′ <: Term′
    op::SortOp
    args::Vector{Term′}
end
Sort′(s::Sort) = Sort′(s.op, s.args)
Sort′(s::SortOp) = Sort′(Sort(s))
DUMMY = Sort′(SortOp(:😃))
@auto_hash_equals struct Var′ <: Term′
    sym::Symbol
    sort::Sort′
    sortvar::Bool
end
Var′(v::Var) = Var′(v.sym, Sort′(v.sort), v.sortvar)
@auto_hash_equals struct App′ <: Term′
    op::TermOp
    sort::Sort′
    args::Vector{Term′}
end
App′(op::TermOp,opsort::Sort′) = App′(op, opsort, Term′[])
App′(op::TermOp,args::Vector{Term′}) = App′(op, DUMMY, args)

function termsort(t::Term′)::Sort′
    if t isa Sort′ return t
    else return t.sort
    end
end

@auto_hash_equals struct EqDecl′
    name::String
    t1::Term′
    t2::Term′
    desc::String
    xtra::Vector{Var′}  # extra assumptions not included in terms
end
@auto_hash_equals struct OpDecl′
    op::TermOp
    sort::Sort′
    args::Vector{Term′}
    desc::String
end

@auto_hash_equals struct SortDecl′
    sort::Sort′
    args::Vector{Term′}
    desc::String
end

Judgment′ = Union{SortDecl′,OpDecl′,EqDecl′}
@auto_hash_equals struct Premises
    premises::OrderedDict{Symbol,Sort′}
end

@auto_hash_equals struct Theory′
    name::String
    sorts::Dict{SortOp,SortDecl′}
    ops::Dict{TermOp,OpDecl′}
    eqs::Set{EqDecl′}
end

VarDict = Dict{Var′,Term′}
VarDict′ = Union{Error,VarDict}

##############################################################################
function Base.show(io::IO, x::SortOp) print(io, x.sym) end
function Base.show(io::IO, x::TermOp) print(io, x.sym) end
function Base.show(io::IO, x::Var)
    printfmt(io, string("({}", x.sortvar ? "::" : ":", "{})"), x.sym, x.sort)
end
function Base.show(io::IO, x::App) printfmt(io, x.op.pat, x.args...) end
function Base.show(io::IO, x::Sort) printfmt(io, x.op.pat, x.args...) end
function Base.show(io::IO, x::SortDecl)
    printfmt(io, "SORTDECL {}", x.sort.op.sym)
end
function Base.show(io::IO, x::OpDecl)
    printfmt(io, "OPDECL {}", x.op.sym)
end
function Base.show(io::IO, x::EqDecl)
    printfmt(io, string("EQ ", x.name, "\n\t{} = {}"), x.t1, x.t2)
end
function Base.show(io::IO, t::Theory)
    println(string(t.name, "\n\n*Sorts*\n"))
    println(io, join(collect(values(t.sorts)), "\n\n"))
    println("\n\n*Operators*\n")
    println(io, join(collect(values(t.ops)), "\n\n"))
    println("\n\n*Axioms*\n")
    println(io, join(collect(t.eqs), "\n\n"))
end
##############################################################################
function Base.isless(x::Op, y::Op)::Bool x.sym < y.sym end
function Base.isless(x::T, y::T)::Bool where {T <: Union{Term,Term′,SortDecl′,OpDecl′,EqDecl′,SortDecl,OpDecl,EqDecl}}
    hash(x) < hash(y)
end
##############################################################################
function Base.length(x::Premises) length(x.premises) end
function Base.length(x::Error) 0 end
##############################################################################
function Base.iterate(x::Premises) iterate(x.premises) end
function Base.iterate(x::Premises, i::Int) iterate(x.premises, i) end
##############################################################################
function Base.size(x::T)::Int where {T <: Union{Term,Term′}}
    if !hasproperty(x, :args) return 1 + size(x.sort)
    else return 1 + sum(map(size, x.args))
    end
end
end