using Test
using MetaGraphs
using LightGraphs

using AlgebraicTypeTheory.Graph
using AlgebraicTypeTheory.GraphTerm

############################################################################
Γ, Δ = [mkVar(x, mkSort(:Ob)) for x in [:Γ,:Δ]]
#
HomΓΓ, HomΓΔ = [mkSort(:Hom, x) for x in [[Γ,Γ], [Γ,Δ]]]
Homδγ = mkApp(:⋅, [mkVar(:δ, HomΓΓ),mkVar(:γ, HomΓΔ)])
@test string(Homδγ) == "⋅(δ:Hom(Γ:Ob, Γ:Ob), γ:Hom(Γ:Ob, Δ:Ob))"
viz(Homδγ.g,true,true,"")
################################################################################
x1, x2, x3, x4, q1, q2, q3, q4 = [mkVar(x, mkSort(:N))
                                  for x in [:x1,:x2,:x3,:x4,:q1,:q2,:q3,:q4]]
x12, x34 = [mkApp(:+, [x,y]) for (x, y) in [[x1,x2],[x3,x4]]]


x = mkApp(:+, [x12,x34])
asc1, asc2 = [mkApp(:+, z) for z in [[q1,mkApp(:+, [q2,q3])], [mkApp(:+, [q1,q2]),q3]]]
@test string(x) == "+(+(x1:N, x2:N), +(x3:N, x4:N))"
Intt = SortDecl(:N, "ℕ", Term[], "Natural Number")
pluss = OpDecl(:+, "binary", mkSort(:N), [x1, x2], "Add two numbers")
asc = Rule("asc", "associative", asc1, asc2)
th = Theory([Intt], [pluss], [asc], "Addition!")

m = patmatch(th.rules[1].t2, infer(th, x))
x_ = uninfer(sub(th.rules[1].t1, m))
@test string(x_) == "+(x1:N, +(x2:N, +(x3:N, x4:N)))"
@test render(th) isa String
validate(th)
################################################################################
@test mkPat(mkPat(x)) == mkPat(x)
@test unPat(infer(th, x)) == x
@test extend(th, [Intt], [pluss], [asc]) == th
@test extend(th, [], [], []) == th
################################################################################
List = SortDecl(:list,"[{}]",[x1],"List of length x1")

lx, lq, lx2,lq2 = [mkVar(v,mkSort(:list,[z])) for (v,z) in
                    zip([:lx,:lq, :lx2,:lq2],[x1,q1,x2,q2])]
ccat = OpDecl(:cat,"{}++{}",mkSort(:list,[mkApp(:+,[x1,x2])]), [lx,lx2], "concatenation")

lth = Theory([Intt,List],[pluss,ccat],nothing,"Lists")

t2 = mkApp(:cat,[lx,lx2])

lx12=mkVar(:e,mkSort(:list,[mkApp(:+, [x1,x2])]))
lx21=mkVar(:f,mkSort(:list,[mkApp(:+, [x2,x1])]))
t = mkApp(:cat,[mkApp(:cat,[lx12,lx12]),mkApp(:cat,[lx21,lx12])])
