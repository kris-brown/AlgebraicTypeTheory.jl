using Test

@testset "Graph" begin
    include("testgraph.jl")
end

@testset "Term" begin
    include("testgraphterm.jl")
end
