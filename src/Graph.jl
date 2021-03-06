module Graph

export
    simplerender, viz,
    MatchDict,Error,patmatch, sub,
    merge_in,subgraph,
    traverse,topsort, argwalk,
    maxv, arity, getarg,root,
    rehash!, rm_dups, addhash,hashindex,compute_hash,
    gethash, getsym, getkind,
    symmetrize,
    NodeType, VarNode, AppNode, SortNode, WildCard, SortedApp,
    add_vertprop!, add_edgeprop!,
    mergeIn!

using LightGraphs: star_digraph, path_digraph, nv,ne, adjacency_matrix, vertices, edges, add_vertex!, add_edge!,rem_edge!, neighbors, AbstractGraph, rem_edge!, has_edge, inneighbors,dijkstra_shortest_paths
using MetaGraphs: MetaDiGraph, set_prop!, set_props!, props, filter_vertices, set_indexing_prop!, get_prop, has_prop
using Colors: @colorant_str
using GraphPlot: spring_layout
using Random: rand, randstring
using PlotlyJS: scatter, Plot, Layout, attr, savefig
using SHA: sha256
using NetworkLayout:Buchheim
using LinearAlgebra: normalize, norm
using Formatting: format
using DataStructures: OrderedDict

"""
Tools for operating on a specific class of LightGraphs - namely acyclic term graphs
"""
############################################################################
# TYPES #
#########
struct Error
    err::String
end

MatchDict = Dict{Symbol,MetaDiGraph}
MatchDict′ = Union{Error,MatchDict}
@enum NodeType VarNode = 1 AppNode = 2 SortNode = 3 WildCard = 4 SortedApp = 5 Unknown = 6
############################################################################

function simplerender(g::MetaDiGraph, n::Int = 0)::String
    n = n == 0 ? root(g) : n
    kind = getkind(g, n)
    sym = string(get_prop(g, n, :sym))

    if kind in [AppNode, SortNode, Unknown, WildCard, SortedApp]
        arty = arity(g, n)
        if arty == 0 return sym end
        pat = string("{}(", join(repeat(["{}"], arty), ", "), ")")
        args = [simplerender(g, getarg(g, n, i)) for i in 1:arty]
        if kind == SortedApp
            args = length(args) > 1 ? vcat(args[2:end], [args[1]]) : args
            pat = replace(pat, ", {})" => ")::{}")
        end
        return format(pat, sym, args...)
    elseif kind == VarNode
        return format("{}:{}", sym, simplerender(g, neighbors(g, n)[1]))
    else
        throw(DomainError)
    end
end

nodecolor = [colorant"lightseagreen", colorant"orange", colorant"lightblue",
             colorant"grey", colorant"pink", colorant"red"]
nodeshapes = ["diamond","circle","square","cross","star","x"]
function viz(g::MetaDiGraph, ids::Bool = false,
             hashs::Bool=false, name::String = "", dryrun::Bool = false)::Nothing

    # Helper funcs
    rotate = (vv,θ) -> [cos(θ) -sin(θ);sin(θ) cos(θ)] * vv
    vizedge = v -> v == [1] ?  "" : join(sort(v), ",")
    vizsym = x -> x == nothing ? "?" : string(x)

    # Collect metadata
    nodedata = [(i, props(g, i)) for i in vertices(g)]
    edgedata = [vizedge(get(props(g, e), :args, Int[])) for e in edges(g)]
    nodelabel = [string(
        (hashs && has_prop(g, i, :hash)) ? "[$(gethash(g, i, true))] " : "",
        ids ? "$i " : "", vizsym(get(d, :sym, "?")),) for (i, d) in nodedata]
    hovertext = [string(ids ? "" : "$i ",hashs ? "" : gethash(g,i,true))
                 for i in vertices(g)]
    membership = [get(d, :kind, nothing) for (_, d) in nodedata]
    inds = [i == nothing ? length(nodecolor) : Int(i) for i in membership]
    nodefill = nodecolor[inds] # default to final color
    nodeshape = nodeshapes[inds]

    if nv(g) < 5
        pos = [(0,1),(-1,0),(1,0),(0,-1)][1:nv(g)]
        locs_x, locs_y = [Vector{Float16}(collect(z)) for z in zip(pos...)]

    else

    if length(traverse(g,root(g)))==nv(g) # root is a true root
        # Create a tree from the DAG using Dijkstra's Algorithm
        d = dijkstra_shortest_paths(g,root(g),allpaths=true)
        g′ = copy(g)
        for e in edges(g′) rem_edge!(g′,e) end
        for e in edges(g′) rem_edge!(g′,e) end


        @assert ne(g′) == 0 "$(collect(edges(g′)))"
        for (i,j) in enumerate(d.predecessors)
            if i == root(g) ? nothing : add_edge!(g′,j[1],i) end
        end
        @assert ne(g′) == nv(g)-1 "$(ne(g′)) != $(nv(g)-1)"

        # Get initial guess for the layout from this tree
        adj = Array(g′.graph.fadjlist)
        pos = Buchheim.layout(adj)
        locs_x, locs_y = [Vector{Float16}(collect(z)) for z in zip(pos...)]
        locs_x, locs_y = spring_layout(g, locs_x, locs_y,C=10,MAXITER=60,INITTEMP=.4)
    else
        locs_x, locs_y = spring_layout(g,C=20,MAXITER=100,INITTEMP=2.)
    end

    end
    scale = max(max(locs_x...)-min(locs_x...),max(locs_y...)-min(locs_y...))
    small = .03 * scale #heuristic for size of arrowheads
    nodes = scatter(;x=locs_x, y=locs_y,mode="markers+text",text=nodelabel,
                    hovertext = hovertext,
                    hovermode="closest", name="nodes",
                    marker=attr(symbol=nodeshape,size=30,color=nodefill),
                    hoverinfo=(ids&&hashs) ? "none" : "text+hovertext")

    edge_traces = []
    for v in vertices(g)
        vv = [locs_x[v];locs_y[v]]
        ns = neighbors(g,v)

        if !isempty(ns)
            ex, ey, et = [],[],[]
            for n in ns
                vn = [locs_x[n];locs_y[n]]
                vect = vn-vv # src -> tar vector
                vn = vv+vect*(norm(vect)/(norm(vect)+small)) # scale back endpoint
                mid  = (vv*2 + vn)/3
                vup,vdown = [normalize(rotate(vect,-x))*small for x in [.3, -.3]]
                arrup, arrdown = [vn - vz for vz in [vup, vdown]]
                append!(ex,[vv[1],mid[1],vn[1],arrup[1], vn[1],arrdown[1],nothing])
                append!(ey,[vv[2],mid[2],vn[2],arrup[2], vn[2],arrdown[2],nothing])
                append!(et,[nothing,vizedge(get_prop(g,v,n,:args)),
                            nothing, nothing,nothing,nothing, nothing])
            end
            append!(edge_traces,[scatter(;x=ex,y=ey,text=et,mode="lines+text", hoverinfo="none",
                                        name=nodelabel[v],line_color=nodefill[v])])
        end
    end
    axis = attr(showline=false, # hide axis line, grid, ticklabels and  title
                zeroline=false, showgrid=false, showticklabels=false,
                scaleanchor="x", scaleratio=1)
    layout = Layout(plot_bgcolor="#E5E5E5", paper_bgcolor="white",title=simplerender(g),
                font_size=10, xaxis=axis,yaxis=axis,hovermode="closest", titlefont_size=14)
    p = Plot([edge_traces...,nodes],layout)
    tmp = string(tempname(),"_",name,".html")
    savefig(p, tmp)
    if !dryrun
        run(Cmd(["open", tmp]))
    end

    return nothing
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
"""Take a MetaDiGraph and add it disjointly to an existing MetaDiGraph
Return index of where the merged-in graph ended up within original graph.

This may result in a graph which has either one or two roots
"""
function merge_in(g::MetaDiGraph, h::MetaDiGraph)::Tuple{MetaDiGraph,Int}
    g = copy(g)
    n_orig = nv(g)
    first(g.indices)  # throws error if graph lacks :hash as an indexing prop
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
    @assert nv(g) >= n_orig "Should only gain nodes, not lose any"
    return (g, hashindex(g, hhash))
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
    args = Vector{Int}[]
    for neigh in ns
        if n in getargs(g, src, neigh) return neigh
        else push!(args, getargs(g, src, neigh)) end
    end
    viz(g, true)
    throw(DomainError("Cannot access arg $n from node $src $(getsym(g,src))\n$args")) # bad arg to high or bad labels)
end

"""Merge dictionaries but check for consistency of definitions"""
function mergeIn!(x::Dict{Symbol,MetaDiGraph},y::Dict{Symbol,MetaDiGraph}
                  )::Nothing
    for (k,v) in y
        if haskey(x,k)
            @assert gethash(v)==gethash(x[k])
        else
            x[k] = v
        end
    end
    return nothing
end

""" Naive structural pattern matching"""
function patmatch(pat::MetaDiGraph, x::MetaDiGraph, sortctx::Dict{String, MetaDiGraph})
    gkeys = [:kind, :sym]
    proot, xroot = [root(g) for g in [pat, x]]
    patkindsym = [get_prop(pat, proot, k) for k in gkeys]
    xkindsym = [get_prop(x, xroot, k) for k in gkeys]
    if patkindsym[1] == VarNode
        patsort = subgraph(pat, getarg(pat, proot, 1))
        xsort = xkindsym[1]==VarNode ? subgraph(x, getarg(x, xroot, 1)) : sortctx[gethash(x)]
        return merge(Dict(patkindsym[2] => x), patmatch(patsort,xsort,sortctx))
    elseif patkindsym != xkindsym
        return Error("Toplevel: $patkindsym != $xkindsym")
    else
        res = Dict{Symbol,MetaDiGraph}()
        for i in 1:arity(pat, proot)
            subpat = subgraph(pat, getarg(pat, proot, i))
            subx = subgraph(x, getarg(x, xroot, i))
            subsol = patmatch(subpat, subx, sortctx)
            if subsol isa Error return subsol end
            mergeIn!(res, subsol)
        end
        return res
    end
end

"""Do I need to treat special case of root being a variable?"""
function sub(pat::MetaDiGraph, d::MatchDict)::MetaDiGraph
    pat = copy(pat)
    debug = false 
    wcs = collect(filter_vertices(pat, :kind, VarNode))
    for wc in wcs
        g = d[getsym(pat, wc)]
        if gethash(g) != gethash(pat, wc)  # pattern var is replaced with something different
            pat, newhead = merge_in(pat, g)
            for inn in inneighbors(pat, wc)
                add_edgeprop!(pat, inn, newhead, getargs(pat, inn, wc))
                rem_edge!(pat, inn, wc)
            end
        end
    end

    out = rehash!(subgraph(pat))
    set_indexing_prop!(out, :hash)
    return out
end

"""
We care about all the possible paths from root to a given wildcard symbol
This recursively gets them all.
"""
function paths_to_sym(g::MetaDiGraph, path::Vector{Int}=Int[],node::Int=0,
                      )::Dict{Symbol,Set{Vector{Int}}}
    node = node == 0 ? root(g) : node

    if getkind(g,node) == VarNode
        return Dict{Symbol,Set{Vector{Int}}}(getsym(g,node)=>Set([path]))
    else
        subsols = [paths_to_sym(g,vcat(path,[i]),getarg(g,node,i))
                    for i in 1:arity(g,node)]

        return isempty(subsols) ? Dict{Symbol,Set{Vector{Int}}}() : merge(subsols...)
    end
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
        viz(out, true, false, "err_end")
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
    for i in collect(vertices(g))
        if getkind(g, i) == SortedApp
            for n in neighbors(g, i)
                @assert set_prop!(g, i, n, :args, [i-1 for i in get_prop(g, i, n, :args)])
            end
            @assert rem_edge!(g, i, getarg(g, i, 1)) "error removing sort"
        end
    end

    g = rehash!(subgraph(g))
    set_indexing_prop!(g, :hash)
    return g
end


#=
Rewriting logic possible handled by SMT instead?
"""
Try to match p2 to x and then sub result into p1
Return the substitution and whether any change was made
"""
function rewrite_toplevel(x::MetaDiGraph, p1::MetaDiGraph, p2::MetaDiGraph, force::Bool=false)::Tuple{MetaDiGraph,Bool}
    p2match = patmatch(p2, x)
    if p2match isa Error
        if force @assert false Error end
        out = x  # p2 did not match, so we cannot rewrite
    else
        out = sub(p1,p2match)  # the standard p2 -> p1 rewrite
    end
    return (out, gethash(out)!=gethash(x))
end

"""Return the rewrite and whether or not x changed"""
function rewrite_at_node(x::MetaDiGraph, i::Int, p1::MetaDiGraph,
                         p2::MetaDiGraph)::Tuple{MetaDiGraph,Bool}
    subg, ihsh = subgraph(x, i), gethash(x, i)
    hshx = gethash(x)
    subres, changed = rewrite_toplevel(subg, p1, p2)
    if !changed
        # println("\t\t\tno match!")
        out= x
    else # need to stitch the subgraph back into the original
        # println("\t\t\tChange! $(simplerender(subg))\n\t\t\t->$(simplerender(subres))")
        new_x, subres_head = merge_in(x, subres)
        new_i = hashindex(new_x, ihsh)
        for inn in inneighbors(new_x,new_i)
            @assert add_edgeprop!(new_x,inn,subres_head,get_prop(x,inn,new_i,:args))
            @assert rem_edge!(new_x,inn,new_i)
            # println("\t\t\tadded $inn->$subres_head, removed $inn->$new_i")
        end
        if i == root(x)  set_prop!(new_x, :root, subres_head) end
        out = rehash!(subgraph(new_x))  # discard elements of subg not in subres
    end
    return (out, gethash(out)!=gethash(x))
end

"""Repeatedly apply rewrite rules at top level and on subterms until convergence.
Naive solution, try to apply every rule at every level (top to bottom). Whenever
we make a change, restart the process. If we make it through the whole term, then
there are no rewrites we can make.

Important case to consider: suppose both p1 and p2 match x? E.g. a rule which says ∀x,y∈X: x=y or (x+y)=(y+x)
In this case, we take the lexicographically smaller (by hash) term. Same for larger cycles.
"""
function rewrite(x::MetaDiGraph,rules::Vector{Tuple{MetaDiGraph,MetaDiGraph}})::MetaDiGraph
    terms = OrderedDict{String,MetaDiGraph}(gethash(x)=>x)

    modified = true
    # println("Starting rewrite")
    while modified
        modified = false
        for i in vertices(x)  # arbitrary order
            # println("\t$i")
            if getkind(x,i) in [SortedTerm, SortNode]  # only two kinds of equalities: sort and term
                for (p1, p2) in rules
                    println("\t\trule $(simplerender(p2))->$(simplerender(p1))")
                    new_x, modified = rewrite_at_node(x, i, p1, p2)
                    if modified
                        # println("\n\tChange made! $(simplerender(x))->$(simplerender(new_x))")
                        newhsh = gethash(new_x)
                        if haskey(terms, newhsh)
                            # println("Cycle detected")
                            start, maxhsh,maxterm = false, "", nothing
                            for (h,t) in terms
                                # println(">> $(simplerender(t))")
                                if h > maxhsh maxhsh, maxterm = h, t end
                            end
                            return maxterm
                        else
                            terms[newhsh] = new_x
                            x = new_x
                        end
                    end
                    if modified break end
                end
                if modified break end
            end
        end
    end
    # println("no changes can be made $(simplerender(x))")
    return x
end =#

end



#=
"""
    Check if structure of pattern matches structure of graphterm recursively.
If we encounter a (labeled) wildcard in the pattern, record the subgraph that it corresponds to.
If the same wildcard label gets matched to two different subgraphs, then throw error.

Naive structural pattern matching
"""
function patmatch(pat::MetaDiGraph, x::MetaDiGraph, path::Vector{Int}=Int[])
    # println("Entering patmatch $path with \n\tpat $(simplerender(pat))\n\tx=$(simplerender(x))")
    gkeys = [:kind, :sym]
    proot, xroot = [root(g) for g in [pat, x]]
    patkindsym = [get_prop(pat, proot, k) for k in gkeys]
    xkindsym = [get_prop(x, xroot, k) for k in gkeys]

    # base case: match a wild card
    if patkindsym[1] == WildCard
        return Dict(Symbol(path, patkindsym[2]) => x)
    end
    # base case: failure
    if patkindsym != xkindsym
        return Error("Toplevel: $patkindsym != $xkindsym")
    end
    # recursive case: combine subsolutions
    np, nx = [neighbors(g, r) for (g, r) in zip([pat, x], [proot, xroot])]
    subsols = MatchDict()
    keep = Set{Symbol}()
    for i in 1:arity(pat, proot)
        subpat = subgraph(pat, getarg(pat, proot, i))
        subx = subgraph(x, getarg(x, xroot, i))
        keep = union(keep,[getsym(subpat,i) for i in
                           filter_vertices(subpat,:kind,WildCard)])
        subsol = patmatch(subpat, subx, vcat(path,[i]))

        ssstr = subsol isa Error ? string(subsol) : join(["$k $(simplerender(v))" for (k,v) in subsol],"\n")
        # println("$path Subsol $i with \n\tpat $(simplerender(pat))\n\tx=$(simplerender(x))\n$(ssstr)")
        if subsol isa Error return subsol end
        for (k, v) in collect(subsol)
            if haskey(subsols, k)
                h1 = gethash(subsols[k], root(subsols[k]))
                h2 = gethash(v, root(v))
                if h1 != h2
                    viz(pat,false,false,"errpat"); viz(x, false,false,"errx")
                    errs0 = "Currpat $(simplerender(subpat))\nCurrx $(simplerender(subx))"
                    errs1 = ["Subsols $k $(simplerender(v))" for (k,v) in subsols]
                    errs2 = ["Curr $k $(simplerender(v))" for (k,v) in subsol]
                    errs = ["$path.$i $(simplerender(subsols[k])) != $(simplerender(v))",errs0, errs1...,errs2...]
                    return Error(join(errs,"\n"))
                end
            else
                subsols[k] = v
            end
        end
        end

    if isempty(path)
        syms = paths_to_sym(pat)
        res = Dict{Symbol,MetaDiGraph}()
        # println("SUBSOLS KEYS $(keys(subsols))")
        # println("SYMS $syms")
        for (k,vs) in syms
            for v in vs
                sym = Symbol(v,k)
                @assert haskey(subsols,sym)
                if haskey(res,k)
                    @assert res[k] == subsols[sym]
                else
                    res[k] = subsols[sym]
                end
            end
        end
        return res
    else
        return subsols
    end
end
=#