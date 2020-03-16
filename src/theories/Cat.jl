module Cat
export cat
using AlgebraicTypeTheory.GraphTerm: Sort, Var, App, OpDecl, SortDecl, Term, Rule, Theory, render, uninfer, infer, patmatch, sub
Ob = Sort(:Ob)
Obdecl = SortDecl(:Ob, "Object of category")
α, β, θ, A, B, C, D, Γ, Δ, Ξ = [Var(x, Ob) for x in [:α,:β,:θ,:A,:B,:C,:D,:Γ,:Δ,:Ξ]]
Hom_aa, Hom_bb, Hom_ab, Hom_bc, Hom_ac, Hom_cd, Hom_αα, Hom_ββ, Hom_αβ, Hom_αθ, Hom_βθ, Hom_ΔΓ, HomΞΔ = [Sort(:Hom, x) for x in [ [A,A],[B,B],[A,B],[B,C],[A,C],[C,D],[α,α],[β,β],[α,β],[α,θ],[β,θ],[Δ,Γ],[Ξ,Δ]]]
f, g, h, γ, δ = [Var(x, h) for (x, h) in zip([:f,:g,:h,:γ,:δ], [Hom_ab,Hom_bc,Hom_cd,Hom_αβ,Hom_βθ])]

Homdecl = SortDecl(:Hom, 2, [α, β], "Hom-set of morphisms from α to β")
iddecl = OpDecl(:id, 1, Hom_αα, [α], "The identity morphism")

cmpdecl = OpDecl(:cmp, "({} ⋅ {})", Hom_αθ, [γ,δ], "Composition, only defined for pairs of morphisms that match head-to-tail, is an associative operation which picks out a third.")

idA, idB = [App(:id, [x]) for x in [A,B]]
fg, gh = [App(:cmp, x) for x in [[f,g],[g,h]]]

f_gh, fg_h = [App(:cmp, x) for x in [[fg,h],[f,gh]]]

idldecl = Rule("⋅ left-identity", f, App(:cmp, [idA,f]))
idrdecl = Rule("⋅ right-identity", f, App(:cmp, [f,idB]))
ascdecl = Rule("⋅ associativity", f_gh, fg_h)

cat = Theory([Obdecl,Homdecl], [iddecl,cmpdecl], [idldecl,idrdecl,ascdecl], "Category")


# Tests
idfg = App(:cmp, [idA,fg])
m = patmatch(cat.rules[1].t2, infer(cat, idfg))
rewritten = uninfer(sub(cat.rules[1].t1, m))
@assert render(cat,rewritten) == "(f ⋅ g)"
# println(render(cat))
end
"""
####################################
# ******* Theory: Category ******* #
####################################

2 sorts, 2 ops, 3 rules

#########
# Sorts #
#########

==================================================

--------   Ob
Ob  sort

Object of category


==================================================
    α,β:Ob
--------------   Hom
Hom(α,β)  sort

Hom-set of morphisms from α to β


##############
# Operations #
##############

==================================================
      α:Ob
----------------   id
id(α) : Hom(α,α)

The identity morphism


==================================================
γ:Hom(α,β)  α,β,θ:Ob  δ:Hom(β,θ)
--------------------------------   ⋅
       (γ ⋅ δ) : Hom(α,θ)

Composition, only defined for pairs of morphisms that match head-to-tail, is an associative operation which picks out a third.


###################
# Equality Axioms #
###################

==================================================
f:Hom(A,B)  g:Hom(B,C)  A,B,C,D:Ob  h:Hom(C,D)
----------------------------------------------   ⋅ associativity
   ((f ⋅ g) ⋅ h) = (f ⋅ (g ⋅ h)) : Hom(A,D)


==================================================
    f:Hom(A,B)  A,B:Ob
--------------------------   ⋅ left-identity
f = (id(A) ⋅ f) : Hom(A,B)


==================================================
    f:Hom(A,B)  A,B:Ob
--------------------------   ⋅ right-identity
f = (f ⋅ id(B)) : Hom(A,B)
"""