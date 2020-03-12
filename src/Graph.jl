module Graph
export Rewrite,
    simplerender, viz,
    MatchDict,
    merge_in,
    traverse,
    subgraph,
    maxv,
    arity, getarg,
    patmatch,
    sub,
    rehash!,
    rm_dups,
    addhash,
    gethash, getsym, getkind,
    symmetrize,
    NodeType,
    VarNode,
    AppNode,
    SortNode,
    WildCard,
    SortedTerm,
    add_vertprop!,
    add_edgeprop!,
    root,
    Error,
    compute_hash,
    hashindex,
    topsort,
    argwalk

using LightGraphs:
    star_digraph,
    path_digraph,
    nv,
    vertices,
    edges,
    add_vertex!,
    add_edge!,
    neighbors,
    AbstractGraph,
    rem_edge!,
    has_edge,
    inneighbors
using MetaGraphs:
    MetaDiGraph, set_prop!, set_props!, props, filter_vertices, set_indexing_prop!, get_prop, has_prop
using Colors: @colorant_str
using GraphPlot: gplot
using Compose: draw, PDF, cm
using Random: rand, randstring
import Cairo, Fontconfig
using Formatting: format
using SHA: sha256

############################################################################
# TYPES #
#########
"""Take structures that look like t2 and rewrite them to look like t1"""
struct Rewrite
    t1::MetaDiGraph{Int64,Float64}
    t2::MetaDiGraph{Int64,Float64}
end
struct Error
    err::String
end
MatchDict = Dict{Symbol,MetaDiGraph}
MatchDict′ = Union{Error,MatchDict}
@enum NodeType VarNode = 1 AppNode = 2 SortNode = 3 WildCard = 4 SortedTerm = 5 Unknown = 6

function simplerender(g::MetaDiGraph, n::Int = 0)::String
    n = n == 0 ? root(g) : n
    kind = getkind(g, n)
    sym = string(get_prop(g, n, :sym))

    if kind in [AppNode, SortNode, Unknown, WildCard]
        arty = arity(g, n)
        if arty == 0 return sym end
        pat = string("{}(", join(repeat(["{}"], arty), ", "), ")")
        args = [simplerender(g, getarg(g, n, i)) for i in 1:arty]
        return format(pat, sym, args...)
    elseif kind == VarNode
        return format("{}:{}", sym, simplerender(g, neighbors(g, n)[1]))
    elseif kind == SortedTerm
        nextkind = getkind(g, getarg(g, n, 2))
        if nextkind == VarNode
            return simplerender(g, getarg(g, n, 2))
        elseif nextkind == WildCard
            return string(getsym(g, getarg(g, n, 2)))
        else
            if nextkind != AppNode nextkind
                println("Warning, SortedNode $n points to $nextkind")
            end
            return format("{}::{}",
                simplerender(g, getarg(g, n, 2)),
                simplerender(g, getarg(g, n, 1)))
        end
    else
        throw(DomainError)
    end
end
############################################################################
"""Take an ordinary graph and add metadata in a conservative way."""
function addhash(g::AbstractGraph)::MetaDiGraph
    newg = MetaDiGraph(g)
    for n in vertices(newg)
        sym = Symbol(randstring(3))
        dic = Dict(:hash => string(sym), :sym => sym, :kind => Unknown)
        @assert set_props!(newg, n, dic)
        for (i, nei) in enumerate(neighbors(newg, n))
            @assert set_prop!(newg, n, nei, :args, [i])
        end
    end
    set_indexing_prop!(newg, :hash)
    set_prop!(newg, :root, 1) # assume 1 is root
    return newg
end

function symmetrize(g::T)::T where {T <: AbstractGraph}
    g = copy(g)
    for e in edges(g)
        add_edge!(g, e.dst, e.src)
    end
    return g
end
############################################################################
# VISUALIZATION #
#################
function viz(
    g::MetaDiGraph{Int64,Float64},
    ids::Bool = false,
    hashes::Bool = false,
    dryrun::Bool = false,
)::Nothing
    nodecolor = [
        colorant"lightseagreen",
        colorant"orange",
        colorant"lightblue",
        colorant"pink",
        colorant"grey",
        colorant"red",
    ]

    function vizedge(v::Vector{Int})::String
        if v == [1]
            return ""
        else
            return join(sort(v), ",")
        end
    end

    function vizsym(x::Union{Nothing,String,Symbol})::String
        return x == nothing ? "?" : string(x)
    end
    nodedata = [(i, props(g, i)) for i in vertices(g)]
    edgedata = [vizedge(get(props(g, e), :args, Int[])) for e in edges(g)]
    nodelabel = [
        string(
            (hashes && has_prop(g, i, :hash)) ? "[$(gethash(g, i, true))] " : "",
            ids ? "$i " : "",
            vizsym(get(d, :sym, "?")),
        ) for (i, d) in nodedata
    ]
    membership = [get(d, :kind, nothing) for (_, d) in nodedata]
    nodefill = nodecolor[[i == nothing ? length(nodecolor) : Int(i) for i in membership]] # default to final color
    graph = gplot(
        g,
        edgelabel = edgedata,
        nodelabel = nodelabel,
        nodefillc = nodefill,
        edgelabelsize = 20,
        edgelabeldistx = 0.0,
        edgelabeldisty = 0.0,
    )
    pth = tempname()
    draw(PDF(pth, 16cm, 16cm), graph)
    if !dryrun
        run(Cmd(["open", pth]))
    end
    return nothing
end
############################################################################
"""Take a MetaDiGraph and add it disjointly to an existing MetaDiGraph
Return index of where the merged-in graph ended up within original graph.

This may result in a graph which has either one or two roots
"""
function merge_in(g::MetaDiGraph, h::MetaDiGraph)::Tuple{MetaDiGraph,Int}
    g = copy(g)
    first(g.indices)
    hhash = gethash(h, root(h))
    reindex = Dict{Int,Int}() # map indices in h to the new joint graph

    for curr in vertices(h)
        hsh = gethash(h, curr)
        hashmatch = collect(filter_vertices(g, :hash, hsh))
        if isempty(hashmatch)
            add_vertex!(g)
            next = maxv(g)
            reindex[curr] = next
            for k in [:kind, :sym]
                @assert set_prop!(g, next, k, get_prop(h, curr, k))
            end
            set_indexing_prop!(g, next, :hash, gethash(h, curr))
        else
            reindex[curr] = hashmatch[1]  # already exists in G
        end
    end

    for e in edges(h)
        add_edgeprop!(g, reindex[e.src], reindex[e.dst], get_prop(h, e, :args))
    end

    h_root = collect(filter_vertices(g, :hash, hhash))[1]
    # None of the hash values from either Graph should have to change...
    # rehash_rec!(g, root(g))
    # rehash_rec!(g, root(h)) # now all nodes have been updated
    return (g, h_root)
end
function len(g::MetaDiGraph, node::Int = 0)::Int
    node = node == 0 ? root(g) : node  # default to root
    subprob = [len(g, n) for n in neighbors(g, node)]
    return 1 + (isempty(subprob) ? 0 : maximum(subprob))
end

function getsym(g::MetaDiGraph, node::Int = 0)::Symbol
    node = node == 0 ? root(g) : node  # default to root
    return get_prop(g, node, :sym)
end
function gethash(g::MetaDiGraph, node::Int = 0, short::Bool=false)::String
    node = node == 0 ? root(g) : node  # default to root
    out = get_prop(g, node, :hash)
    return short ? out[1:3] : out
end
function getkind(g::MetaDiGraph, node::Int = 0)::NodeType
    node = node == 0 ? root(g) : node  # default to root
    return get_prop(g, node, :kind)
end

function getargs(g::MetaDiGraph, src::Int, dst::Int)::Vector{Int}
    get_prop(g, src, dst, :args)
end

"""Start at a node and traverse DFS/BFS, recording order nodes were seen
Node that the order branches are traversed is not determined (the natural
ordering from :args in the edges is not used...yet)
"""
function traverse(g::MetaDiGraph, start::Int = 0, dfs::Bool = true)::Vector{Int}
    start = start == 0 ? root(g) : start
    seen = Vector{Int}()
    visit = Vector{Int}([start])
    @assert start in vertices(g) "can't access $start in $(props(g, 1))"
    while !isempty(visit)
        next = pop!(visit)
        if !(next in seen)
            for n in neighbors(g, next)
                if !(n in seen)
                    if dfs append!(visit, n) else insert!(visit, 1, n) end
                end
            end
            push!(seen, next)
        end
    end
    return seen
end

"""Make a subgraph out of all descendents with a given node as root"""
function subgraph(g::MetaDiGraph, start::Int = 0)::MetaDiGraph
    start = start == 0 ? root(g) : start

    inds = traverse(g, start)
    newgraph = MetaDiGraph()
    set_indexing_prop!(newgraph, :hash)
    set_prop!(newgraph, :root, 1)
    reindex = Dict{Int,Int}()

    for (newi, i) in enumerate(inds)  # in DFS order
        add_vertex!(newgraph)
        for m in [:sym, :kind]
            set_prop!(newgraph, newi, m, get_prop(g, i, m))
        end
        set_indexing_prop!(newgraph, newi, :hash, gethash(g, i))
        reindex[i] = newi
    end

    for e in edges(g)
        src, tar = get(reindex, e.src, nothing), get(reindex, e.dst, nothing)
        if !(nothing in [src, tar])
            add_edgeprop!(newgraph, src, tar, getargs(g, e.src, e.dst))
        end
    end
    return newgraph
end
############################################################################
"""Maximum vertex value"""
function maxv(g::MetaDiGraph)::Int
    maximum(vertices(g))
end
function root(g::MetaDiGraph)::Int
    get_prop(g, :root)
end
"""Look at edge data with arg index information to determine arity."""
function arity(g::MetaDiGraph, node::Int = 0)::Int
    node = node == 0 ? root(g) : node
    ns = neighbors(g, node)
    if isempty(ns) return 0 end
    edgeargs = [getargs(g, node, n) for n in ns]
    return max([max(ea...) for ea in edgeargs]...)
end

"""Get the n'th argument from a node, where the arg indices are in edge metadata"""
function getarg(g::MetaDiGraph, src::Int, n::Int)::Int
    @assert n > 0 "Illegal argument index $n"
    ns = neighbors(g, src)
    for neigh in ns
        if n in getargs(g, src, neigh) return neigh end
        end
    throw(DomainError("Cannot access arg $n from node $src")) # bad arg to high or bad labels)
end



"""
Important case to consider: suppose both p1 and p2 match x? E.g. a rule which says ∀x,y∈X: x=y or (x+y)=(y+x)
In this case, we take the lexicographically smaller (by hash) term.

Return the substitution and whether any change was made
"""
function rewrite_toplevel(x::MetaDiGraph, p1::MetaDiGraph, p2::MetaDiGraph)::Tuple{MetaDiGraph,Bool}
    p1match = patmatch(p1, x)
    p2match = patmatch(p2, x)
    if !(p1match isa Error || p2match isa Error) # both match
        out = p1 < p2 ? sub(p1, p1match) : sub(p2, p2match)
    elseif p2match isa Error # neither or just p1 matched
        out = x  # p2 did not match, so we cannot rewrite
    else # p2 matched, p1 didn't
        out = sub(p1,p1match)  # the standard p2 -> p1 rewrite
    end
    return (out, out==x)
end



"""
    Check if structure of pattern matches structure of graphterm recursively.
If we encounter a (labeled) wildcard in the pattern, record the subgraph that it corresponds to.
If the same wildcard label gets matched to two different subgraphs, then throw error.

NOTE under a theory, two subgraphs that seem different may in fact be equal, so maybe this
function should just return the list of patterns that get matched to, and the function caller
can determine whether this is really an error or not.

Concern: a variable in some top level operation uses the same variable in some nested
operation. When we recursively match variables, there can be a name collision.
"""
function patmatch(pat::MetaDiGraph, x::MetaDiGraph)
    keys = [:kind, :sym]
    proot, xroot = [root(g) for g in [pat, x]]
    patkindsym = [get_prop(pat, proot, k) for k in keys]
    xkindsym = [get_prop(x, xroot, k) for k in keys]

    # base case: match a wild card
    if patkindsym[1] == WildCard
        return Dict(patkindsym[2] => x)
    end
    # base case: failure
    if patkindsym != xkindsym
        return Error("Toplevel: $patkindsym != $xkindsym")
    end
    # recursive case: combine subsolutions
    np, nx = [neighbors(g, r) for (g, r) in zip([pat, x], [proot, xroot])]
    subsols = MatchDict()
    for i in 1:arity(pat, proot)
        subpat = subgraph(pat, getarg(pat, proot, i))
        subx = subgraph(x, getarg(x, xroot, i))
        subsol = patmatch(subpat, subx)
        if subsol isa Error return Error("$i.$(subsol.err)") end
        for (k, v) in collect(subsol)
            if haskey(subsols, k)
                h1 = gethash(subsols[k], root(subsols[k]))
                h2 = gethash(v, root(v))
                if h1 != h2
                    viz(pat); viz(x)
                    errs0 = "Currpat $(simplerender(subpat))\nCurrx $(simplerender(subx))"
                    errs1 = ["Subsols $k $(simplerender(v))" for (k,v) in subsols]
                    errs2 = ["Curr $k $(simplerender(v))" for (k,v) in subsol]
                    errs = ["$i. $(simplerender(subsols[k])) != $(simplerender(v))",errs0, errs1...,errs2...]
                    return Error(join(errs,"\n"))
                end
            else
                subsols[k] = v
            end
        end
        end
    # up = uninfer(pat)
    # vars = [getsym(up,i) for i in filter_vertices(up, :kind, WildCard)]
    return subsols # MatchDict(k=>v for (k,v) in subsols if k in vars) # maybe we need vars of pat instead?
end

function sub(pat::MetaDiGraph, d::MatchDict)::MetaDiGraph
    pat = copy(pat)

    for wc in collect(filter_vertices(pat, :kind, WildCard))
        g = d[getsym(pat, wc)]
        pat, newhead = merge_in(pat, g)
        for inn in inneighbors(pat, wc)
            add_edgeprop!(pat, inn, newhead, getargs(pat, inn, wc))
            rem_edge!(pat, inn, wc)
            end
        end

    out = subgraph(pat)
    out = rehash!(out)
    set_indexing_prop!(out, :hash)
    return out
end

"""Compute hash, assuming neighbors' hashes are correctly computed."""
function compute_hash(g::MetaDiGraph, node::Int)::String
    hs = [gethash(g, getarg(g, node, i)) for i in 1:arity(g, node)]
    return bytes2hex(sha256(join([getsym(g, node), getkind(g, node), hs...])))
end

"""Assume all hash values are incorrect and need to be recomputed.
Modifies metadata of an existing MetaGraph (removes :hash as
indexing property)"""
function rehash_rec!(g::MetaDiGraph, node::Int)::Nothing
    for n in neighbors(g, node) rehash_rec!(g, n) end
    @assert set_prop!(g, node, :hash, compute_hash(g, node))
    return nothing
end

function rehash!(g::MetaDiGraph, preferred::Set{Int} = Set{Int}())::MetaDiGraph
    g = copy(g)
    g.indices = Set{Symbol}()
    rehash_rec!(g, root(g))
    return rm_dups(g, preferred)
end

"""Assume a particular node's hash has changed. Recompute it, then
work recursively upwards until we reach the root.
function rehashup!(g::MetaDiGraph, node::Int)::String
   IS THIS FUNCTION USEFUL? """

"""Condense nodes such that things with identical hash are merged.
Will return a metagraph with :hash set as indexing prop. For graphs where same
hash means identical substructure, it does not matter that an arbtirary node of
that hash value is kept."""
function rm_dups(g::MetaDiGraph, preferred::Set{Int})::MetaDiGraph
    trav = length(traverse(g, root(g)))
    @assert trav == nv(g) "Can only quotient graphs with a root: $(simplerender(g)) has $trav / $(nv(g)) from root $(root(g))"
    keep_nodes = Dict{String,Int}() # get_prop(g, root(g), :hash) => root(g))
    for v in sort(vertices(g))
        h = gethash(g, v)
        if !haskey(keep_nodes, h) || v in preferred
            keep_nodes[h] = v
        end
    end
    g_ = copy(g) # don't modify input
    keep = Set(values(keep_nodes))
    for e in edges(g_)
        if !(e.src in keep) @assert rem_edge!(g_, e)
        elseif !(e.dst in keep)
            args = get_prop(g_, e, :args)
            newtar = keep_nodes[gethash(g_, e.dst)]
            if !has_edge(g_, e.src, newtar)
                @assert add_edgeprop!(g_, e.src, newtar, Int[])
            end
            oldargs = getargs(g_, e.src, newtar)
            newargs = sort(vcat(oldargs, args))
            @assert set_prop!(g_, e.src, newtar, :args, newargs)
            @assert rem_edge!(g_, e)
        end
    end
    for e in edges(g_)
        @assert has_prop(g_, e, :args)
    end
    out = subgraph(g_, root(g_))
    if length(keep_nodes) != nv(out) || any([!(has_prop(out, e, :args)) for e in edges(out)])
        println("keep_nodes $(sort([(v, k[1:3]) for (k, v) in keep_nodes]))")
        viz(out, true, true)
        throw(Exception(simplerender(g)))
    end
    return out # discard anything not connected to root
end

function add_edgeprop!(g::MetaDiGraph, src::Int, dst::Int, arg::Vector{Int})::Bool
    a = add_edge!(g, src, dst)
    b = set_prop!(g, src, dst, :args, arg)
    return a && b
end
    """Add a new node with a dict of metadata."""
function add_vertprop!(g::MetaDiGraph, p::Dict)::Int
    @assert add_vertex!(g)
    new = maxv(g)
    @assert set_props!(g, new, p)
    return new
    end
    """Get vertex associated with a hash. Throw error if not found."""
function hashindex(g::MetaDiGraph, hsh::String, safe::Bool = false)::Union{Nothing,Int}
    hashmatch = collect(filter_vertices(g, :hash, hsh))

    if length(hashmatch) == 1 return hashmatch[1]
    elseif safe return nothing
    else throw(DomainError("Bad hash $(hsh[1:3]) in $(simplerender(g)): $(length(hashmatch)) matches"))
    end
        end
function topsort!(g::MetaDiGraph, v::Int, visit::Set{Int}, stack::Vector{Int})::Vector{Int}
    push!(visit, v)
    for n in neighbors(g, v)
        if !(n in visit) topsort!(g, n, visit, stack) end
    end
    insert!(stack, 1, v)
end
function topsort(g::MetaDiGraph)::Vector{Int}
visit = Set{Int}()
stack = Vector{Int}([])
for v in vertices(g) # start the process from each node
    if !(v in visit) topsort!(g, v, visit, stack) end
end
return stack
end

"""
Return a subgraph starting at a node dictated by a initial node
and a sequence of steps, e.g. take arg #1, then arg #2, etc.
"""
function argwalk(g::MetaDiGraph, steps::Vector{Int},start::Int=0)::MetaDiGraph
    curr = start == 0 ? root(g) : start
    for step in steps
        curr = getarg(g, curr, step)
    end
    return subgraph(g,curr)
end
function uninfer(g::MetaDiGraph)::MetaDiGraph
    g = copy(g)
    if getkind(g) == SortedTerm
        newroot = getarg(g, root(g), 2)
        @assert rem_edge!(g, root(g), getarg(g, root(g), 1)) # for good measure
        @assert rem_edge!(g, root(g), getarg(g, root(g), 2)) # for good measure
        set_prop!(g, :root, newroot)
    end
    for i in collect(vertices(g))
        for j in collect(neighbors(g, i))
            if getkind(g, j) == SortedTerm
                tar = getarg(g, j, 2)
                @assert add_edgeprop!(g, i, tar, get_prop(g, i, j, :args)) "error adding $i -> $tar"
                @assert rem_edge!(g, i, j) "error removing $i->$j"
            end
        end
    end

    g = rehash!(subgraph(g))
    set_indexing_prop!(g, :hash)
    return g
end
end


