using Test

@testset "Graph" begin
    include("testgraph.jl")
end

@testset "Term" begin
    include("testgraphterm.jl")
end

@testset "Inst" begin
    include("testinst.jl")
end

@testset "Norm" begin
    include("testnorm.jl")
end
