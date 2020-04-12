using Test
using MetaGraphs
using LightGraphs

if isdefined(@__MODULE__, :LanguageServer)
    include("../src/Graph.jl")
    include("../src/GraphTerm.jl")
    using .Graph
    using .GraphTerm
else
    using AlgebraicTypeTheory.Graph
    using AlgebraicTypeTheory.GraphTerm
end

############################################################################
Γ, Δ = [Var(x, Sort(:Ob)) for x in [:Γ,:Δ]]
#
HomΓΓ, HomΓΔ = [Sort(:Hom, x) for x in [[Γ,Γ], [Γ,Δ]]]
Homδγ = App(:⋅, [Var(:δ, HomΓΓ),Var(:γ, HomΓΔ)])
@test string(Homδγ) == "⋅(δ:Hom(Γ:Ob, Γ:Ob), γ:Hom(Γ:Ob, Δ:Ob))"
viz(Homδγ.g,true,true,"",true)
################################################################################
x1, x2, x3, x4, q1, q2, q3, q4 = [Var(x, Sort(:N))
                                  for x in [:x1,:x2,:x3,:x4,:q1,:q2,:q3,:q4]]
x12, x34 = [App(:+, [x,y]) for (x, y) in [[x1,x2],[x3,x4]]]


x = App(:+, [x12,x34])
asc1, asc2 = [App(:+, z) for z in [[q1,App(:+, [q2,q3])], [App(:+, [q1,q2]),q3]]]
@test string(x) == "+(+(x1:N, x2:N), +(x3:N, x4:N))"
Intt = SortDecl(:N, "ℕ", Term[], "Natural Number")
pluss = OpDecl(:+, "binary", Sort(:N), [x1, x2], "Add two numbers")
asc = Rule("asc", "associative", asc1, asc2)
th = Theory([Intt], [pluss], [asc], "Addition!", true)
xx = infer(th, x.g) # what to test about this?
th_ = Theory([Intt], [pluss], [asc], "Addition!")

@test render(th_) isa String
validate(th)

################################################################################
#@test extend(th, [Intt], [pluss], [asc]) == th
#@test extend(th, [], [], []) == th
################################################################################
#=List = SortDecl(:list,"[{}]",[x1],"List of length x1")

lx, lq, lx2,lq2 = [Var(v,Sort(:list,[z])) for (v,z) in
                    zip([:lx,:lq, :lx2,:lq2],[x1,q1,x2,q2])]
ccat = OpDecl(:cat,"{}++{}",Sort(:list,[App(:+,[x1,x2])]), [lx,lx2], "concatenation")

lth = Theory([Intt,List],[pluss,ccat],nothing,"Lists")

t2 = App(:cat,[lx,lx2])

lx12=Var(:e,Sort(:list,[App(:+, [x1,x2])]))
lx21=Var(:f,Sort(:list,[App(:+, [x2,x1])]))
t = App(:cat,[App(:cat,[lx12,lx12]),App(:cat,[lx21,lx12])])
=#