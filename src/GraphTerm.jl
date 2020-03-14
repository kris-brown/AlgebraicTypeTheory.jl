module GraphTerm
export rewrite,
    Term, Theory, SortDecl, OpDecl, Rule, validate,join_term,
    Sort, App,Var, mkPat, unPat,
    viz, simplerender, render, root, getkind, patmatch, sub,
    infer, infer!, uninfer,
    vars, getSig, extend, upgrade

using MetaGraphs: MetaDiGraph, get_prop, has_prop, set_prop!, set_props!, set_indexing_prop!, props, filter_vertices
using AutoHashEquals: @auto_hash_equals
using LightGraphs: nv, ne, vertices, edges, neighbors, inneighbors, maxsimplecycles, add_edge!, has_edge, rem_edge!
using SparseArrays: blockdiag
using Formatting: FormatExpr, printfmt, format
using SHA: sha256
import Base: hash, isless, (==)

if isdefined(@__MODULE__, :LanguageServer)
    include("../src/Graph.jl")
    using .Graph
else
    using AlgebraicTypeTheory.Graph
    import AlgebraicTypeTheory.Graph: root, arity, viz, getkind, patmatch, sub, simplerender, uninfer
end
############################################################################

"""Nodes are annotated with kind::NodeType and sym::Symbol
Edges are annotated with args::[Int] to express multigraph properties
"""
struct Term
    g::MetaDiGraph{Int64,Float64}
    Term(g) = new(validate(g))
end

"""pat determines how Sort is rendered. Args are terms which act as patterns
to typecheck when the sort is applied."""
@auto_hash_equals struct SortDecl
    sym::Symbol
    pat::String
    args::Vector{Term}
    desc::String
    SortDecl(sym, pat, args, desc) = new(
        sym,
        pat == "binary" ? string("({} ", sym, " {})") :
            (
            pat == 0 ? string(sym) :
                (pat isa Int ? string(sym, "(", join(repeat(["{}"], pat), ","), ")") : pat)
        ),
        args,
        desc,
    )
end
SortDecl(s::Symbol, d::String) = SortDecl(s, 0, Term[], d)


"""Sort field variables are related to args: pattern matching on the args here
should inform how to compute what the sort is of an application of Op."""
@auto_hash_equals struct OpDecl
    sym::Symbol
    pat::Union{Int,String}
    sort::Term
    args::Vector{Term}
    desc::String
    OpDecl(sym, pat, sort, args, desc) = new(
        sym,
        pat == "binary" ? string("({} ", sym, " {})") :
            (pat isa Int ? string(sym, "(", join(repeat(["{}"], pat), ","), ")") : pat),
        sort,
        args,
        desc,
    )

end
OpDecl(s::Symbol, o::Term, d::String) = OpDecl(s, 0, o, Term[], d)
OpDecl(s::Symbol, p::String, o::Term, d::String = "") = OpDecl(s, p, o, Term[], d)

@auto_hash_equals struct Rule
    name::String
    desc::String
    t1::Term
    t2::Term
end
Rule(n::String, t1::Term, t2::Term) = Rule(n, "", t1, t2)

@auto_hash_equals struct Premises
    premises::Dict{Symbol,Term}
end

@auto_hash_equals struct Theory
    sorts::Dict{Symbol,SortDecl}
    ops::Dict{Symbol,OpDecl}
    rules::Vector{Rule}
    name::String
    upgraded::Bool
    Theory(sorts, ops, rules, name, upgraded) =
        upgraded ? new(sorts, ops, rules, name, upgraded) :
        upgrade(new(sorts, ops, rules, name, upgraded))
end
Theory(s::Union{Nothing,Vector{SortDecl}}, o::Union{Nothing,Vector{OpDecl}}, r::Union{Nothing,Vector{Rule}}, n::String)  = Theory(
    Dict{Symbol,SortDecl}(s === nothing ? [] : [(x.sym, x) for x in s]),
    Dict{Symbol,OpDecl}(o === nothing ? [] : [(x.sym, x) for x in o]),
    Vector{Rule}(r === nothing ? [] : r),
    n,
    false,
)

"""Longest chain length"""
function Base.length(t::Term)::Int
    len(t.g)
end

function Base.show(io::IO, t::Term)::Nothing
    print(io, simplerender(t.g))
end
function Base.isless(x::Term, y::Term)::Bool
    gethash(x.g) < gethash(y.g)
end
function Base.:(==)(x::Term, y::Term)::Bool
    gethash(x.g) == gethash(y.g)
end
function Base.isless(x::T, y::T)::Bool where {T<:Union{SortDecl,OpDecl}}
    x.sym < y.sym
end
function Base.isless(x::Rule, y::Rule)::Bool
    x.name < y.name
end
"""Total # of nodes"""
function Base.size(t::Term)::Int nv(t.g) end
function Base.hash(t::Term)::UInt64 hash(gethash(t.g)) end
function Base.hash(r::Rule)::UInt64
    sum([hash(r.name), hash(r.desc), hash(r.t1), hash(r.t2)])
end
function Base.hash(r::SortDecl)::UInt64
    sum([hash(r.sym), hash(r.pat), hash(r.desc), [hash(a) for a in r.args]...])
end
function Base.hash(r::OpDecl)::UInt64
    sum(vcat(
        [hash(r.sym), hash(r.pat), hash(r.sort), hash(r.desc)],
        [hash(a) for a in r.args],
    ))
end

############################################################################
function viz(t::Term, ids::Bool = false, hshs::Bool=false,name::String = "")::Nothing
    viz(t.g, ids, hshs, name)
end
function root(t::Term)::Int
    root(t.g)
end
function simplerender(t::Term)::String
    simplerender(t.g)
end
function getkind(t::Term)::NodeType
    getkind(t.g, root(t))
end
function arity(t::Term)::Int
    arity(t.g, root(t))
end
function patmatch(p::Term, x::Term)
    patmatch(p.g, x.g)
end
function sub(p::Term, m::MatchDict)::Term
    Term(sub(p.g, m))
end
############################################################################
"""Normally, for t2->t1, we need FreeVar(t1)⊆FreeVar(t2), however there is an edge case which breaks this
Consider ∀x,y∈X: x=y, asserting that X is singleton. The freevars do not intersect, but we can still
perform rewrites (using lexicographic ordering). So it seems like there's nothing formally to check
for Rules other than that their terms are well-formed, unfortunately.
"""
function validate(t::Theory, r::Rule)::Nothing
    terms = [r.t1.g, r.t2.g]
    [validate(t, x) for x in terms]
    return nothing
end

function validate(t::Theory)::Theory
    [validate(t, d) for d in values(t.sorts)]
    [validate(t, d) for d in values(t.ops)]
    [validate(t, d) for d in t.rules]
    return t
end

function validate(t::Theory, x::SortDecl)::Nothing
    [validate(t, a) for a in x.args]
    @assert length(x.args) == sym_arity(x)
    return nothing
end
function validate(t::Theory, x::OpDecl)::Nothing
    [@assert getkind(a) == SortedTerm for a in x.args]
    [validate(t, a) for a in x.args]
    validate(t, x.sort)
    @assert length(x.args) == sym_arity(x)
    return nothing
end

function vars(t::Term)::Dict{Symbol,Term}
    vars = collect(filter_vertices(t.g, :kind, VarNode))
    if isempty(vars)
        wcs = collect(filter_vertices(t.g, :kind, WildCard))
        Dict([
            (getsym(t.g, v), Term(subgraph(t.g, getarg(t.g, inneighbors(t.g, v)[1], 1))))
            for v in wcs
        ])
    else
        return Dict([
            (getsym(t.g, v), Term(subgraph(t.g, neighbors(t.g, v)[1]))) for v in vars
        ])
    end
end

function validate(t::Theory, x::Term)::Term
    g = x.g  # we already validated non-theory aspects when constructing the Term
    vars = collect(filter_vertices(g, :kind, VarNode))
    err = "Same variable appears with different hashes"
    @assert length(vars) == length(Set([getsym(g, v) for v in vars])) err
    validate(t, g)
    return x
end

function validate(t::Theory, g::MetaDiGraph, n::Int = 0)::Nothing
    n = n == 0 ? root(g) : n
    kind = getkind(g, n)
    sym = getsym(g, n)
    ns = neighbors(g, n)
    ar = arity(g, n)
    if kind == SortNode
        @assert haskey(t.sorts, sym)
        decl = t.sorts[sym]
        @assert ar == sym_arity(decl)
    elseif kind == AppNode
        @assert haskey(t.ops, sym)
        decl = t.ops[sym]
        @assert ar == sym_arity(decl)
    elseif kind == VarNode
        @assert ar == 1
    end
    for n in ns
        validate(t, g, n)
    end
    return nothing
end

"""Make sure the metagraph instance is well-formed"""
function validate(g::MetaDiGraph)::MetaDiGraph
    # Make sure all nodes/edges have the right metadata existing
    @assert has_prop(g, :root)
    reqkeys = [:kind, :hash, :sym]
    keytypes = [NodeType, String, Symbol]
    for i in vertices(g)
        p = props(g, i)
        for (k, X) in zip(reqkeys, keytypes)
            @assert haskey(p, k) "Node $i missing required key $k: $(props(g, i))"
            @assert p[k] isa X "Node $i key $k has bad type $(typeof(p[k]))"
        end
    end
    for e in edges(g)
        @assert haskey(props(g, e), :args) "Edge $e missing required key :args"
    end
    # Initialize variables
    groot = root(g)
    var_seen = Set{Symbol}() # keep track of VarNode symbols
    is_inferred = !isempty(filter_vertices(g, :kind, SortedTerm))
    # Misc overall checks
    @assert length(traverse(g, groot)) == nv(g) "Root node must see everything"
    @assert nv(g) > 0 "Term must not be empty"
    @assert g.indices == Set(Symbol[:hash]) ":hash must be an indexing prop"
    @assert maxsimplecycles(g) == 0 "Graph has $(maxsimplecycles(g)) cycles"
    ids = [gethash(g, i) for i in vertices(g)]
    @assert length(ids) == length(unique(ids)) "Graph has nonunique ids"
    varnodes, wcs = [collect(filter_vertices(g, :kind, k)) for k in [VarNode, WildCard]]
    @assert isempty(varnodes) || isempty(wcs) "Can have wildcards $wcs (if a pattern) or variables $varnodes (if not) but not both!"

    # More in-depth checks on each node
    for i in vertices(g)
        inn = inneighbors(g, i)
        err = "Node $i shouldn't be an input iff is root (callers: $(inn))"
        @assert isempty(inn) == (i == groot) err
        ns = neighbors(g, i)
        kind = getkind(g, i)
        sym = getsym(g, i)

        if is_inferred && kind in [VarNode, AppNode]
            @assert length(inn) == 1 "If inferred, all Vars/Apps should be the lone child (of a SortedTerm) $inn"
            innkind = getkind(g, inn[1])
            @assert innkind == SortedTerm "If inferred, all Vars/Apps should the lone child of a SortedTerm: $innkind"
        end

        if kind == VarNode
            @assert length(ns) == 1 "VarNodes have only one child, not $(length(ns))"
            @assert getkind(g, ns[1]) == SortNode "VarNode must be connected to a SortNode"
            @assert !(sym in var_seen) "Same symbol $sym with different types"
            push!(var_seen, sym)
        elseif kind == SortedTerm
            sta1, sta2 = [getarg(g, i, z) for z in 1:2]
            @assert length(ns) == 2 "SortedTerm has two children, not $(length(ns))"
            @assert getkind(g, sta1) == SortNode "First arg of SortedTerm is a sort $(getkind(g, sta1))"
            if !(getkind(g, sta2) in [AppNode, VarNode, WildCard])
                println("Error with $(simplerender(g))")
                viz(g, true, false, "sortedtermerror")
            end
            @assert getkind(g, sta2) in [AppNode, VarNode, WildCard] "Second arg of SortedTerm is Var/App/WildCard: $(getkind(g, sta2))"

        elseif kind == WildCard
            @assert length(ns) == 0 "Wildcard has no children"
        elseif kind in [SortNode, AppNode]
            if !isempty(ns)
                edgeargs = [get_prop(g, i, n, :args) for n in ns]
                ari = arity(g, i)
                args = sort(vcat(edgeargs...))
                @assert collect(1:ari) == args "Bad arg labeling: $edgeargs"
                if is_inferred
                    @assert all([getkind(g, n) == SortedTerm for n in ns])
                end
            end
        else
            @assert false "Illegal node kind $kind"
        end
    end
    return g
end
############################################################################
function join_term(sym::Symbol, kind::NodeType, args::Vector{Term})::Term
    base = MetaDiGraph{Int64,Float64}(1)
    h = bytes2hex(sha256(join([sym, kind, [gethash(x.g) for x in args]...])))
    set_props!(base, 1, Dict(:sym => sym, :kind => kind))
    set_prop!(base, :root, 1)
    set_indexing_prop!(base, 1, :hash, h)
    for (i, arg) in enumerate(args)
        base, arghead = merge_in(base, arg.g)
        if !has_edge(base, 1, arghead)
            add_edgeprop!(base, 1, arghead, Int[])
        end
        arg_inds = get_prop(base, 1, arghead, :args)
        set_prop!(base, 1, arghead, :args, vcat(arg_inds, [i]))
    end
    newg = rehash!(base)
    if gethash(newg) != h
        println("joinTerm $sym $kind $([simplerender(a) for a in args])")
        viz(base, false,true, "jointermErrBase")
        viz(newg, false,true, "jointermErrNewG")
    end
    @assert gethash(newg) == h
    return Term(newg)
end
############################################################################
function Sort(sym::Symbol, args::Vector{Term} = Term[])::Term
    @assert all([getkind(a) in [AppNode, VarNode] for a in args]) "mkApp arg fail $args"
    join_term(sym, SortNode, args)
end
function App(sym::Symbol, args::Vector{Term} = Term[])::Term
    @assert all([getkind(a) in [AppNode, VarNode] for a in args]) "mkApp arg fail $args"
    join_term(sym, AppNode, args)
end
function Var(sym::Symbol, sort::Term)::Term
    @assert getkind(sort) == SortNode
    join_term(sym, VarNode, [sort])
end

"""Interpret a term as a pattern for matching. All variables Var(Varsym)->Sort
are replaced with Wildcard(Varsym) and outgoing edge removed"""
function mkPat(t::Term)::Term Term(mkPat(t.g)) end

"""Convert variables into wildcards.
Under normal circumstances only advisable to call on inferred terms."""
function mkPat(g::MetaDiGraph)::MetaDiGraph
    g = copy(g)
    groot = root(g)
    vars = collect(filter_vertices(g, :kind, VarNode))
    @assert !(groot in vars) "Cannot make a pattern out of a variable"
    for v in vars
        for n in neighbors(g, v)
            rem_edge!(g, v, n)
        end
        set_prop!(g, v, :kind, WildCard)
    end
    g_ = subgraph(g)
    g_ = rehash!(g_)
    set_indexing_prop!(g_, :hash)
    return g_
end
function unPat(t::Term)::Term
    Term(unPat(t.g))
end

"""Take an INFERRED pattern and make an UNINFERRED term (wildcards replaced w/ variables)"""
function unPat(g::MetaDiGraph)::MetaDiGraph
    vars = collect(filter_vertices(g, :kind, WildCard))
    for v in vars
        inn = inneighbors(g, v)
        @assert length(inn) == 1 && getkind(g, inn[1]) == SortedTerm
        sortnode = getarg(g, inn[1], 1)
        add_edgeprop!(g, v, sortnode, [1])
        set_prop!(g, v, :kind, VarNode)
    end
    return uninfer(g)
end

############################################################################
function get_deps(x::SortDecl)::Set{Symbol}
    isempty(x.args) ? Set{Symbol}() : union([get_deps(a) for a in x.args]...)
end
function get_deps(x::OpDecl)::Set{Symbol}
    union(get_deps(x.sort), [get_deps(a) for a in x.args]...)
end
function get_deps(x::Term)::Set{Symbol}
    res = Set{Symbol}()
    for v in vertices(x.g)
        if getkind(x.g, v) in [SortNode, AppNode]
            push!(res, getsym(x.g, v))
        end
    end
    return res
end

"""Return ordered list of symbols that respects dependencies"""
function symdag(t::Theory)::Vector{Symbol}
    deps = MetaDiGraph()
    for k in keys(merge(t.sorts, t.ops))
        add_vertprop!(deps, Dict(:sym => k))
    end
    set_indexing_prop!(deps, :sym)
    for (k, v) in merge(t.sorts, t.ops)
        for d in get_deps(v)
            add_edge!(deps, deps[d, :sym], deps[k, :sym])
        end
    end
    return [getsym(deps, v) for v in topsort(deps)]
end

"""There are terms and sorts referred to within the theory, which serve as
patterns to be matched against other terms."""
function upgrade(t::Theory)::Theory
    # println("upgrading $(t.name)")
    syms = symdag(t)
    # println("symdag $syms")
    for sym in syms
        #println("Upgrading $sym")
        isop = haskey(t.ops, sym)
        decl = isop ? t.ops[sym] : t.sorts[sym]
        udecl = upgrade(t, decl)
        newsorts = isop ? t.sorts : Dict{Symbol,SortDecl}(t.sorts..., sym => udecl)
        newops = isop ? Dict{Symbol,OpDecl}(t.ops..., sym => udecl) : t.ops
        t = Theory(newsorts, newops, t.rules, t.name, true)
    end
    rules = [upgrade(t, s) for s in t.rules]
    return validate(Theory(t.sorts, t.ops, rules, t.name, true))
end
function upgrade(t::Theory, s::SortDecl)::SortDecl
    # println("upgrading $s\n************")
    newargs = Term[]
    for (i, a) in enumerate(s.args)
        # println("upgrading sort $(s.sym) arg $i")
        push!(newargs, infer(t, a))
    end

    return SortDecl(s.sym, s.pat, [mkPat(a) for a in newargs], s.desc)
end
function upgrade(t::Theory, o::OpDecl)::OpDecl
    # println("upgrading $o\n************")
    newsort = mkPat(infer(t, o.sort))
    newargs = Term[]
    for (i, a) in enumerate(o.args)
        # println("upgrading op $(o.sym) arg $i")
        push!(newargs, infer(t, a))
    end
    return OpDecl(o.sym, o.pat, newsort, [mkPat(a) for a in newargs], o.desc)
end

"""Assumes that the theory has already been bootstrapped/upgrade"""
function upgrade(t::Theory, r::Rule)::Rule
    # println("upgrading $r\n************")
    t1 = mkPat(infer(t, r.t1))
    t2 = mkPat(infer(t, r.t2))
    Rule(r.name, r.desc, t1, t2)
end

############################################################################

"""Infer the sort of an appnode. Modify it to become a SortedNode
We may need to use rewrite rules even at this step?
"""
function infer(th::Theory, t::Term)::Term
    sts = isempty(collect(filter_vertices(t.g, :kind, SortedTerm)))
    if !sts
        viz(t, false, true,"alreadyinferred")
        @assert false "Cannot infer something already inferred: $(simplerender(t)) $sts"
    end
    res = infer!(th, copy(t.g))
    try
        return Term(res)
    catch m
        viz(t.g, true,false,"inferErrorG")
        viz(res, false,true, "inferErrorRes")
        throw(m)
    end
end

function infer!(th::Theory, g::MetaDiGraph)::MetaDiGraph
    println("STARTING INFER W/ $(simplerender(g))")
    seen = Set{String}()
    preferred = sort(collect(vertices(g)))  # when reindexing, default to these values
    first(g.indices) # make sure we have :hash index
    function next()::Union{Int,Nothing}  # take something leafside
        for v in vertices(g)
            if (
                !(gethash(g, v) in seen) &&
                Set([gethash(g, e) for e in neighbors(g, v)]) ⊆ seen
            )
                return v
            end
        end
    end

    n = next()
    while !(n === nothing)
        sorti = nothing
        sym, kind = [get_prop(g, n, x) for x in [:sym, :kind]]
        viewhsh = gethash(g, n, true)
        inds = [x[1:3] for x in seen]
        println("$viewhsh $sym $kind seen $(sort(inds))")
        if kind == VarNode
            sorti = neighbors(g, n)[1]
        elseif kind == AppNode
            matches = MatchDict[]
            op_pat = th.ops[sym].sort
            infered_args = th.ops[sym].args
            for i in 1:arity(g, n)
                argpat = infered_args[i]
                argterm_ = subgraph(g, getarg(g, n, i))
                set_indexing_prop!(argterm_, :hash)
                argterm = Term(argterm_) # make sure this is well-formed
                validate(th, argterm.g)
                if getkind(argterm) != SortedTerm
                    viz(g,false, true,"BadArgterm")
                    @assert false "Bad argterm $(getarg(g, n, i)) is not SortedTerm"
                end
                m = patmatch(argpat, argterm)
                if m isa Error
                    #viz(argpat, true); viz(argterm, true)
                    viz(g,false, false,"inferPatmatchErr")
                    @assert false "$sym @ $viewhsh arg $i: $(m.err)"
                end
                push!(matches, m)
            end
            newsort = isempty(matches) ? op_pat : sub(op_pat, merge(matches...))
            first(g.indices)
            # what we substituted was already inferred
            g, sorti = merge_in(g, newsort.g)
            for i in traverse(g, sorti)
                ghi = gethash(g, i)
                if !(ghi in seen)
                    println("\tadding $(ghi[1:3]) from sort")
                    push!(seen, gethash(g, i))
                    if getkind(g,i)==SortedTerm
                        child = getarg(g,i,2)
                        for inn in inneighbors(g,child)
                            if !(gethash(g,inn) in seen)
                                add_edgeprop!(g, inn, i, get_prop(g,inn,child,:args))
                                rem_edge!(g,inn,child)
                            end
                        end
                    end
                end
            end

        elseif kind in [SortNode, SortedTerm] # pass
        else
            viz(g,false,false,"DomainError")
            throw(DomainError("$(simplerender(g)) $viewhsh $kind"))
        end

        if kind in [AppNode, VarNode]
            st = add_vertprop!(g, Dict(:kind => SortedTerm, :sym => Symbol()))
            set_indexing_prop!(g, st, :hash, compute_hash(g, st))
            println("$n: add $st ")
            if n == root(g)
                @assert set_prop!(g, :root, st)
            else
                println("\t$n $sym inneighbors $(collect(inneighbors(g, n)))")
                for i in collect(inneighbors(g, n))
                    println("\t$(getkind(g, i)) adding $i->$st ($(getkind(g, st))) and removing $i->$n ($(getkind(g, n)))")
                    @assert add_edgeprop!(g, i, st, get_prop(g, i, n, :args))
                    @assert getkind(g, n) in [AppNode, VarNode, WildCard]
                    @assert rem_edge!(g, i, n)
                end
            end
            @assert add_edgeprop!(g, st, sorti, [1])
            @assert add_edgeprop!(g, st, n, [2])
        end

        println("adding $(gethash(g, n,true)) ")

        push!(seen, gethash(g, n))
        seeninds = Set([v for v in vertices(g) if gethash(g, v) in seen])
        g = rehash!(g, seeninds)
        set_indexing_prop!(g, :hash)
        n = next()
    end
    return g # nothing left to infer
end

##############################################################################
"""Remove SortedTerm annotations in graph."""
function uninfer(x::Term)::Term
    Term(uninfer(x.g))
end

function uninfer(s::SortDecl)::SortDecl
    SortDecl(s.sym, s.pat, [unPat(a) for a in s.args], s.desc)
end
function uninfer(s::OpDecl)::OpDecl
    OpDecl(s.sym, s.pat, unPat(s.sort), [unPat(a) for a in s.args], s.desc)

end
function uninfer(s::Rule)::Rule
    Rule(s.name, s.desc, unPat(s.t1), unPat(s.t2))
end
##############################################################################

function rewrite(r::Rule, x::Term)::Term
    Term(sub(r.t1, patmatch(r.t2, x.g)))
end
##############################################################################

function sym_arity(op::T)::Int where {T<:Union{OpDecl,SortDecl}}
    length(Set(FormatExpr(op.pat).entries))
end
##############################################################################
function extend(
    t1::Theory,
    s::Vector{T},
    o::Vector{Q} = OpDecl[],
    r::Vector{R} = Rule[],
    n::String = "",
)::Theory where {T<:Union{Any,SortDecl},Q<:Union{Any,OpDecl},R<:Union{Any,Rule}}
    ss = unique(vcat([uninfer(sd) for sd in values(t1.sorts)], Vector{SortDecl}(s)))
    os = unique(vcat([uninfer(od) for od in values(t1.ops)], Vector{OpDecl}(o)))
    rs = unique(vcat([uninfer(rd) for rd in values(t1.rules)], Vector{Rule}(r)))
    #  has $(length(ss)) sorts $(length(os)) ops $(length(rs)) rules ")
    return Theory(ss, os, rs, isempty(n) ? t1.name : n)
end
##############################################################################


function Base.show(io::IO, x::OpDecl)
    printfmt(io, "OPDECL {}", x.pat)
end
function Base.show(io::IO, x::SortDecl)
    printfmt(io, "SORTDECL {}", x.pat)
end
function Base.show(io::IO, x::Rule)
    printfmt(io, string("EQ ", x.name, "\n\t{} = {}"), x.t1, x.t2)
end

function Base.show(io::IO, t::Theory)
    println(io, string(t.name, "\n\n*Sorts*\n"))
    println(io, join(collect(values(t.sorts)), "\n\n"))
    println(io, "\n\n*Operators*\n")
    println(io, join(collect(values(t.ops)), "\n\n"))
    println(io, "\n\n*Axioms*\n")
    println(io, join(collect(t.rules), "\n\n"))
end

function printRule(top::String, bot::String, name::String, desc::String)::String
    lt, lb = map(length, [top, bot])
    line = '-'^max(lt, lb)
    offt = ' '^((length(line) - lt) ÷ 2)
    offb = ' '^((length(line) - lb) ÷ 2)
    out = join(
        [
            '='^50,
            string(offt, top),
            "$line   $name",
            string(offb, bot),
            isempty(desc) ? "" : "\n$desc\n",
        ],
        '\n',
    )
    return out
end

function render(x::Theory)::String
    function box(s::String)::Vector{String}
        line = '#'^(length(s) + 4)
        return [join([line, string("# ", s, " #"), line], "\n")]
    end
    summ = "$(length(x.sorts)) sorts, $(length(x.ops)) ops, $(length(x.rules)) rules"
    dag = symdag(x)
    judgments = vcat(
        "",
        box("******* Theory: $(x.name) *******"),
        summ,
        box("Sorts"),
        [render(x, x.sorts[v]) for v in dag if haskey(x.sorts, v)]...,
        box("Operations"),
        [render(x, x.ops[v]) for v in dag if haskey(x.ops, v)]...,
        box("Equality Axioms"),
        [render(x, z) for z in sort(collect(x.rules))]...,
    )
    return (join(judgments, "\n\n"))
end

function render(t::Theory, x::SortDecl)::String
    top = render(t, getSig(x))
    if isempty(x.args)
        bot = string(x.pat)
    else
        bot = format(x.pat, [render(t, q) for q in x.args]...)
    end

    return printRule(top, string(bot, "  sort"), string(x.sym), x.desc)
end
function render(t::Theory, x::Premises)::String
    sorts = sort(unique(collect(values(x.premises))))
    dic = Dict(
        [join([string(k) for (k, v) in sort(x.premises) if v == s], ",") => render(t, s) for
        s in sorts],
    )
    return join([string(k, ":", v) for (k, v) in dic], "  ")
end
function render(t::Theory, x::OpDecl)::String
    top = render(t, getSig(x))
    sor = render(t, x.sort)
    bot = string(format(x.pat, [render(t, z) for z in x.args]...), " : ", sor)
    return printRule(top, bot, string(x.sym), x.desc)
end
function render(t::Theory, x::Term)::String
    render(t, x.g)
end
function render(t::Theory, g::MetaDiGraph, n::Int = 0)::String
    n = n == 0 ? root(g) : n
    kind = getkind(g, n)
    sym = getsym(g, n)

    if kind in [SortNode, AppNode]
        isapp = kind == AppNode
        decl = (isapp ? t.ops : t.sorts)[sym]
        pat = decl.pat
        arty = length(decl.args)
        if arty == 0
            return string(sym, isapp ? "()" : "")
        end

        args = [render(t, g, getarg(g, n, i)) for i in 1:arty]
        return format(pat, args...)
    elseif kind in [VarNode, WildCard]
        return string(sym)
    elseif kind == SortedTerm
        return render(t, g, getarg(g, n, 2))
    else
        throw(DomainError)
    end
end

function render(t::Theory, r::Rule)::String
    rsort = subgraph(r.t1.g, getarg(r.t1.g, root(r.t1.g), 1))
    top = render(t, getSig(r))
    sortstr = getkind(r.t1) == SortNode ? "sort" : string(": ",render(t, rsort))
    bot = format("{} = {}   {}", render(t, r.t1), render(t, r.t2), sortstr)
    return printRule(top, bot, r.name, r.desc)
end
##############################################################################
function getSig(x::SortDecl)::Premises
    free = isempty(x.args) ? Dict() : merge([vars(a) for a in x.args]...)
    return Premises(free)
end
function getSig(x::OpDecl)::Premises
    sort = vars(x.sort)
    free = merge(vars(x.sort), [vars(a) for a in x.args]...)
    return Premises(free)
end
function getSig(x::Rule)::Premises
    return Premises(merge(vars(x.t1), vars(x.t2)))
end

end
