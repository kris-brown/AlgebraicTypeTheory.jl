# using Test

using LightGraphs
using MetaGraphs
using SparseArrays: blockdiag

# include("../src/Graph.jl")
# include("../src/GraphTerm.jl")

using AlgebraicTypeTheory.Graph


# Test merge_in!
s4 = addhash(star_digraph(4))
p5 = addhash(path_digraph(5))
s4p5, _ = merge_in(s4, p5)

@test nv(s4p5) == 9
@test ne(s4p5) == 7

# Test quotient
joined_ = blockdiag(s4, p5)
add_edgeprop!(joined_, 1,5,[1])
joined = addhash(joined_)
joined.indices = Set{Symbol}() # allow ourselves to make collisions
set_prop!(joined,2,:hash,gethash(joined, 3))
rmjoined = rm_dups(joined, Set{Int}())
@test nv(rmjoined) == 8
@test ne(rmjoined) == 7

rmj = copy(rmjoined)
for i in 6:7 set_prop!(rmj, i, :sym, :x) end  # these nodes are both terminal
rmj = rehash!(rmj) # now nodes 6&7 are both same hash, get merged
rmj2 = rm_dups(rmj, Set{Int}()) # one of the star ends is merged with tail of the 5-path
@test nv(rmj2) == 7
@test ne(rmj2) == 7
@test simplecycleslength(symmetrize(rmj2))[1][6] == 2 # one bidirectional cycle of size 6
viz(rmj2,true,true,"")


# Test topsort
g = MetaDiGraph([0 1 0 0 0 ; 0 1 0 0 0 ; 1 1 0 0 0 ; 1 0 1 1 0 ; 0 0 1 1 0])
@test topsort(g) == [5,4,3,1,2]