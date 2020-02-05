export cat

using AlgebraicTypeTheory: SortOp, Sort, TermOp, Var, OpDecl, SortDecl, App,
                EqDecl, mkTheory, Judgment,render

#########################################################################
ob, Hom = [SortOp(x,i) for (x,i) in zip([:Ob, :Hom],[0,"({}→{})"])]
Ob = Sort(ob)
α,β,θ,A,B,C,D,Γ,Δ,H = [Var(x,Ob) for x in [:α,:β,:θ,:A,:B,:C,:D,:Γ,:Δ,:H]]

Hom_ab,Hom_bc,Hom_ac,Hom_cd,Hom_αα,Hom_αβ,Hom_αθ,Hom_βθ,Hom_ΔΓ,HomHΔ = [Sort(Hom, x)
    for x in [ [A,B],[B,C],[A,C],[C,D],[α,α],[α,β],[α,θ],[β,θ],[Δ,Γ],[H,Δ]]]

obdecl = SortDecl(Ob, string("Objects of a category are a convenience to make ",
        "it easier to talk about morphisms."))
homdecl = SortDecl(Hom_αβ, [α,β], string("Hom-set, a set of morphisms which ",
        "exists between any pair of objects in a category."))
id = TermOp(:id,1)
iddecl = OpDecl(id, Hom_αα, [α], string("The identity operation picks out a ",
        "particular morphism in Hom(α,α) which satisfies the identity laws."))
Cmp = TermOp(:⋅,"binary")
Cmpdecl = OpDecl(Cmp,Hom_αθ,[Hom_αβ,Hom_βθ],
        string("Composition, only defined for pairs of morphisms that match ",
         "head-to-tail, is an associative operation which picks out a third."))
f, g, h, γ, δ = [Var(x, h) for (x, h) in zip(
        [:f, :g, :h, :γ, :δ], [Hom_ab, Hom_bc, Hom_cd, Hom_ΔΓ, HomHΔ])]
fg, gh = [App(Cmp,x) for x in [[f,g],[g,h]]]
idA,idB = [App(id,[x]) for x in [A,B]]
f_gh, fg_h = [App(Cmp,x) for x in [[fg,h],[f,gh]]]

idldecl = EqDecl("⋅ left-identity", App(Cmp,[idA,f]), f)
idrdecl = EqDecl("⋅ right-identity", App(Cmp,[f,idB]), f)
ascdecl = EqDecl("⋅ associativity", f_gh, fg_h)

cat = mkTheory("Cat",Judgment[obdecl, iddecl, homdecl, Cmpdecl,
                              idldecl, idrdecl, ascdecl])
"""
Rendered theory


###############################
# ******* Theory: Cat ******* #
###############################

#########
# Sorts #
#########

***
α:Ob  β:Ob
-----------   Hom
(α→β)  sort

Hom-set, a set of morphisms which exists between any pair of objects in a category.


***

--------   Ob
Ob  sort

Objects of a category are a convenience to make it easier to talk about morphisms.


##############
# Operations #
##############

***
    α:Ob β:Ob θ:Ob
-----------------------   ⋅
((α→β) ⋅ (β→θ)) : (α→θ)

Composition, only defined for pairs of morphisms that match head-to-tail, is an associative operation which picks out a third.


***
    α:Ob
-------------   id
id(α) : (α→α)

The identity operation picks out a particular morphism in Hom(α,α) which satisfies the identity laws.


###################
# Equality Axioms #
###################

***
  A:Ob  B:Ob  f:(A→B)
-----------------------   ⋅ right-identity
(f ⋅ id(B)) = f : (A→B)


***
A:Ob  B:Ob  C:Ob  D:Ob  f:(A→B)  g:(B→C)  h:(C→D)
-------------------------------------------------   ⋅ associativity
      ((f ⋅ g) ⋅ h) = (f ⋅ (g ⋅ h)) : (A→D)


***
  A:Ob  B:Ob  f:(A→B)
-----------------------   ⋅ left-identity
(id(A) ⋅ f) = f : (A→B)
"""
