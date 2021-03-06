module GraphTerm
export
    Term, Theory, SortDecl, OpDecl, Rule, validate,join_term,
    Sort, App,Var,
    viz, simplerender, render, root, getkind, patmatch, sub,
    infer, uninfer, naiveInfer, getsym, gethash,
    vars, getSig, extend, upgrade,normalize

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
    import AlgebraicTypeTheory.Graph: root, arity, viz, getkind, patmatch, sub, simplerender, uninfer, getsym, gethash, getarg
end
############################################################################

"""Nodes are annotated with kind::NodeType and sym::Symbol
Edges are annotated with args::[Int] to express multigraph properties
"""
struct Term
    g::MetaDiGraph
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
SortDecl(s::Symbol, d::String="") = SortDecl(s, 0, Term[], d)


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
OpDecl(s::Symbol, p::Union{Int,String}, o::Term, d::String = "") = OpDecl(s, p, o, Term[], d)
OpDecl(s::Symbol, o::Term, d::String= "") = OpDecl(s, 0, o, Term[], d)

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
Theory(s::Union{Nothing,Vector{SortDecl}}, o::Union{Nothing,Vector{OpDecl}}, r::Union{Nothing,Vector{Rule}}, n::String, upgrade::Bool=false)  = Theory(
    Dict{Symbol,SortDecl}(s === nothing ? [] : [(x.sym, x) for x in s]),
    Dict{Symbol,OpDecl}(o === nothing ? [] : [(x.sym, x) for x in o]),
    Vector{Rule}(r === nothing ? [] : r),
    n, upgrade,
)

"""Longest chain length"""
function Base.length(t::Term)::Int len(t.g) end

function Base.show(io::IO, t::Term)::Nothing
    print(io, simplerender(t.g))
end
function Base.isless(x::Term, y::Term)::Bool gethash(x) < gethash(y) end
function Base.:(==)(x::Term, y::Term)::Bool gethash(x) == gethash(y) end
function Base.isless(x::T, y::T)::Bool where {T<:Union{SortDecl,OpDecl}}
    x.sym < y.sym
end
function Base.isless(x::Rule, y::Rule)::Bool
    x.name < y.name
end
"""Total # of nodes"""
function Base.size(t::Term)::Int nv(t.g) end
function Base.hash(t::Term)::UInt64 hash(gethash(t)) end
function Base.hash(r::Rule)::UInt64
    sum([hash(r.name), hash(r.desc), hash(r.t1), hash(r.t2)])
end
function Base.hash(r::SortDecl)::UInt64
    sum([hash(r.sym), hash(r.pat), hash(r.desc), [hash(a) for a in r.args]...])
end
function Base.hash(r::OpDecl)::UInt64
    sum(vcat([hash(r.sym), hash(r.pat), hash(r.sort), hash(r.desc)],
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
function gethash(t::Term, short::Bool=false)::String gethash(t.g, root(t), short) end
function getkind(t::Term)::NodeType getkind(t.g, root(t)) end
function getsym(t::Term)::Symbol getsym(t.g, root(t)) end
function arity(t::Term)::Int arity(t.g, root(t)) end
function patmatch(p::Term, x::Term) patmatch(p.g, x.g) end
function sub(p::Term, m::MatchDict)::Term Term(sub(p.g, m)) end
function getarg(t::Term, i::Int)::Term
    Term(subgraph(t.g, getarg(t.g,root(t), i)))
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
    [@assert getkind(a) in [SortedApp, VarNode] for a in x.args]
    [validate(t, a) for a in x.args]
    validate(t, x.sort)
    @assert length(x.args) == sym_arity(x)
    return nothing
end

function vars(t::Term)::Dict{Symbol,Term}
    vars = collect(filter_vertices(t.g, :kind, VarNode))
    if isempty(vars)
        wcs = collect(filter_vertices(t.g, :kind, WildCard))
        Dict([(getsym(t.g, v), Term(subgraph(t.g, getarg(t.g, inneighbors(t.g, v)[1], 1))))
              for v in wcs ])
    else
        return Dict([
            (getsym(t.g, v), Term(subgraph(t.g, neighbors(t.g, v)[1]))) for v in vars
        ])
    end
end

function validate(t::Theory, x::Term)::Term
    g = x.g  # already validated non-theory aspects in construction
    vars = collect(filter_vertices(g, :kind, VarNode))
    err = "Same variable appears with different hashes"
    @assert length(vars) == length(Set([getsym(g, v) for v in vars])) err
    validate(t, g)
    return x
end

"""Confirm nodes have the right number of arguments."""
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
    elseif kind == SortedApp
        @assert haskey(t.ops, sym)
        decl = t.ops[sym]
        @assert ar == sym_arity(decl)+1
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
    is_inferred = !isempty(filter_vertices(g, :kind, SortedApp))
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

        if is_inferred
            @assert kind != AppNode
            if kind in [SortedApp, SortNode]
            for ind in 1:arity(g,i)
                valid = (kind == SortedApp && ind == 1) ? [SortNode] : [VarNode, SortedApp]
                @assert getkind(g, getarg(g,i,ind)) in valid
            end
            end
        end

        if kind == VarNode
            @assert length(ns) == 1 "VarNodes have only one child, not $(length(ns))"
            @assert getkind(g, ns[1]) == SortNode "VarNode must be connected to a SortNode"
            @assert !(sym in var_seen) "Same symbol $sym with different types"
            push!(var_seen, sym)
        elseif kind == WildCard
            @assert length(ns) == 0 "Wildcard has no children"
        elseif kind in [SortNode, AppNode, SortedApp]
            if !isempty(ns)
                edgeargs = [get_prop(g, i, n, :args) for n in ns]
                ari = arity(g, i)
                args = sort(vcat(edgeargs...))
                @assert collect(1:ari) == args "Bad arg labeling: $edgeargs"
            end
        else
            @assert false "Illegal node kind $kind"
        end
    end
    return g
end
############################################################################
function join_term(sym::Symbol, kind::NodeType, args::Vector{Term})::Term
    base = MetaDiGraph(1)
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
#=
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

"""Wildcards replaced w/ variables"""
function unPat(g::MetaDiGraph)::MetaDiGraph
    vars = collect(filter_vertices(g, :kind, WildCard))
    for v in vars set_prop!(g, v, :kind, VarNode) end
    return uninfer(g)
end
=#
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

    return SortDecl(s.sym, s.pat, newargs, s.desc)
end
function upgrade(t::Theory, o::OpDecl)::OpDecl
    # println("upgrading $o\n************")
    newsort = infer(t, o.sort)
    newargs = Term[]
    for (i, a) in enumerate(o.args)
        # println("upgrading op $(o.sym) arg $i")
        push!(newargs, infer(t, a))
    end
    return OpDecl(o.sym, o.pat, newsort, newargs, o.desc)
end

"""Assumes that the theory has already been bootstrapped/upgrade"""
function upgrade(t::Theory, r::Rule)::Rule
    # println("upgrading $r\n************")
    t1 = infer(t, r.t1)
    t2 = infer(t, r.t2)
    Rule(r.name, r.desc, t1, t2)
end

############################################################################

function infer(th::Theory, t::Term)::Term
    Term(infer(th, t.g))
end
function infer(th::Theory, g::MetaDiGraph)::MetaDiGraph
    g = copy(g)
    res = naiveInfer(th, g)

    for (k, v) in res
        app = hashindex(g, k)
        g, head = merge_in(g, v)
        for nei in neighbors(g, app)
            set_prop!(g, app, nei, :args, [i+1 for i in get_prop(g, app, nei, :args)])
        end
        add_edgeprop!(g, app, head, [1])

        set_prop!(g,app,:kind, SortedApp)
    end

    return rehash!(g)
end

function naiveInfer(th::Theory, g::MetaDiGraph, n::Int = 0,
                    res::Dict{String,MetaDiGraph} = Dict{String,MetaDiGraph}()
                   )::Dict{String, MetaDiGraph}
    n = n == 0 ? root(g) : n

    sym, kind = [get_prop(g, n, x) for x in [:sym, :kind]]

    @assert kind != SortedApp "Dont use infer on something already inferred"

    # Recursively solve for descendents
    neighbors =  [getarg(g, n, i) for i in 1:arity(g,n)]

    for neigh in neighbors
        if !haskey(res, gethash(g, neigh))
            merge!(res,naiveInfer(th, g, neigh, res))
        end
    end

    # Add current node if we are App
    if kind == AppNode && !haskey(res, gethash(g, n))
        op_pat = th.ops[sym].sort.g
        args = th.ops[sym].args
        getsort = z -> getkind(g,z) == AppNode ? # either app or var
            res[gethash(g, z)] : subgraph(g, getarg(g, z, 1))
        argsorts = [getsort(nei) for nei in neighbors]
        matches = MatchDict()
        for (pat,neigh) in zip(args,neighbors)
            mat = patmatch(pat.g, subgraph(g, neigh), res)
            if mat isa Error @assert false mat.err end
            mergeIn!(matches, mat)
        end
        res[gethash(g, n)] = sub(op_pat, matches)
    end
    if sym == :cmp
        #println("new res with op pat $(simplerender(op_pat))\n and matches \n\t$(join([(k,simplerender(v)) for (k,v) in matches],"\n\t"))\n and result \n\t$(simplerender((res[gethash(g,n)]))")
        #viz(op_pat)
        #viz(res[gethash(g,n)],false,true)
    end
    return res
end

##############################################################################
"""Remove SortedTerm annotations in graph."""
function uninfer(x::Term)::Term
    Term(uninfer(x.g))
end

function uninfer(s::SortDecl)::SortDecl
    SortDecl(s.sym, s.pat, [uninfer(a) for a in s.args], s.desc)
end
function uninfer(s::OpDecl)::OpDecl
    OpDecl(s.sym, s.pat, uninfer(s.sort), [uninfer(a) for a in s.args], s.desc)

end
function uninfer(s::Rule)::Rule
    Rule(s.name, s.desc, uninfer(s.t1), uninfer(s.t2))
end

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
    nocheck::Bool = false
)::Theory where {T<:Union{Any,SortDecl},Q<:Union{Any,OpDecl},R<:Union{Any,Rule}}
    ss = unique(vcat([uninfer(sd) for sd in values(t1.sorts)], Vector{SortDecl}(s)))
    os = unique(vcat([uninfer(od) for od in values(t1.ops)], Vector{OpDecl}(o)))
    rs = unique(vcat([uninfer(rd) for rd in values(t1.rules)], Vector{Rule}(r)))
    return Theory(ss, os, rs, isempty(n) ? t1.name : n, nocheck)
end

####################################
# Visualization of data structures #
####################################

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

function render(x::Theory, prnt::Bool=false)::String
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
    out = (join(judgments, "\n\n"))
    if prnt println(out) end
    return out
end

function render(t::Theory, x::SortDecl, prnt::Bool=false)::String
    top = render(t, getSig(x))
    if isempty(x.args)
        bot = string(x.pat)
    else
        bot = format(x.pat, [render(t, q) for q in x.args]...)
    end
    out = printRule(top, string(bot, "  sort"), string(x.sym), x.desc)
    if prnt println(out) end
    return out
end

function render(t::Theory, x::Premises, prnt::Bool=false)::String
    sorts = sort(unique(collect(values(x.premises))))
    dic = Dict(
        [join([string(k) for (k, v) in sort(x.premises) if v == s], ",") => render(t, s) for
        s in sorts],
    )
    out = join([string(k, ":", v) for (k, v) in dic], "  ")
    if prnt println(out) end
    return out
end

function render(t::Theory, x::OpDecl, prnt::Bool=false)::String
    top = render(t, getSig(x))
    sor = render(t, x.sort)
    bot = string(format(x.pat, [render(t, z) for z in x.args]...), " : ", sor)
    out = printRule(top, bot, string(x.sym), x.desc)
    if prnt println(out) end
    return out
end

function render(t::Theory, x::Term, prnt::Bool=false)::String
    out = render(t, x.g)
    if prnt println(out) end
    return out
end

function render(t::Theory, g::MetaDiGraph, n::Int = 0, prnt::Bool=false)::String
    n = n == 0 ? root(g) : n
    kind = getkind(g, n)
    sym = getsym(g, n)

    if kind in [SortNode, AppNode, SortedApp]
        isapp = kind in [SortedApp, AppNode]
        issapp = kind == SortedApp
        decl = (isapp ? t.ops : t.sorts)[sym]
        pat = decl.pat

        if isempty(decl.args)
            out = string(pat, isapp ? "()" : "")
        else
            arty = length(decl.args)
            args = [render(t, g, getarg(g, n, i + (issapp ? 1 : 0)))
                    for i in 1:arty]
            out = format(pat, args...)
        end
    elseif  kind in [VarNode, WildCard]
        out = string(sym)
    else
        throw(DomainError)
    end
    if prnt println(out) end
    return out
end

function render(t::Theory, r::Rule, prnt::Bool=false)::String
    rsort = subgraph(r.t1.g, getarg(r.t1.g, root(r.t1.g), 1))
    top = render(t, getSig(r))
    is_inferred = !isempty(filter_vertices(r.t1.g, :kind, SortedApp))
    if is_inferred
        sortstr = getkind(r.t1) == SortNode ? "sort" : string(": ",render(t, rsort))
    else
        sortstr = ""
    end
    bot = format("{} = {}   {}", render(t, r.t1), render(t, r.t2), sortstr)
    out = printRule(top, bot, r.name, r.desc)
    if prnt println(out) end
    return out
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
