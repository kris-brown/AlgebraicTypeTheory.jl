using AlgebraicTypeTheory: extend
using AlgebraicTypeTheory.Theories: boolalg, Bool,top, neg, land, lor
export preorder

############
# Preorder #
############
ob = SortOp(:ob)
Ob = Sort(ob)
obdecl = SortDecl(Ob, "Underlying set of a preorder")

X, Y, Z = [Var(x,Ob) for x in [:x, :y, :z]]

Leq = TermOp(:≤, "binary")
leq = OpDecl(Leq, Bool, [X,Y])
refl = EqDecl("≤ reflexivity", App(top), App(Leq, [X,X]))

tran_subterm = App(neg, [App(land, [App(Leq, [X,Y]), App(Leq, [X,Z])])])

tran = EqDecl("≤ transitivity",
    App(top), App(lor, [tran_subterm, App(Leq, [X,Z])]))

preorder = extend(boolalg, Judgment[obdecl, leq, refl, tran], "Preorder")


"""
Rendered Theory

####################################
# ******* Theory: Preorder ******* #
####################################

#########
# Sorts #
#########

***

----------   Bool
Bool  sort

The underlying set of a boolean algebra


***

--------   ob
ob  sort

Underlying set of a preorder


##############
# Operations #
##############

***
  x:ob y:ob
--------------   ≤
(x ≤ y) : Bool


***

--------   ⊤
⊤ : Bool

Top element, x ∨ ¬x


***
  x:Bool
-----------   ¬
¬(x) : Bool


***
α:Bool β:Bool
--------------   ∨
(α ∨ β) : Bool

Join/Least upper bound


***

--------   ⊥
⊥ : Bool

Bottom element, x ∧ ¬x


***
α:Bool β:Bool
--------------   ∧
(α ∧ β) : Bool

Meet/Greatest lower bound


###################
# Equality Axioms #
###################

***
       x:Bool  y:Bool  z:Bool
------------------------------------   ∨ associativity
(x ∨ (y ∨ z)) = ((x ∨ y) ∨ z) : Bool


***
     x:Bool  y:Bool
------------------------   ∧, ∨ absorption
x = (x ∧ (x ∨ y)) : Bool


***
       x:Bool  y:Bool  z:Bool
------------------------------------   ∧ associativity
(x ∧ (y ∧ z)) = ((x ∧ y) ∧ z) : Bool


***
     x:Bool  y:Bool
------------------------   ∨, ∧ absorption
x = (x ∨ (x ∧ y)) : Bool


***
     x:Bool  y:Bool
------------------------   ∨ symmetry
(x ∨ y) = (y ∨ x) : Bool


***
          x:Bool  y:Bool  z:Bool
------------------------------------------   ∧ ∨ distributivity
(x ∧ (y ∨ z)) = ((x ∧ y) ∨ (x ∧ z)) : Bool


***
       x:ob
------------------   ≤ reflexivity
⊤ = (x ≤ x) : Bool


***
      x:Bool
------------------   ∧ identity
x = (x ∧ ⊤) : Bool


***
     x:Bool  y:Bool
------------------------   ∧ symmetry
(x ∧ y) = (y ∧ x) : Bool


***
      x:Bool
------------------   ∨ identity
x = (x ∨ ⊥) : Bool


***
              x:ob  y:ob  z:ob
---------------------------------------------   ≤ transitivity
⊤ = (¬(((x ≤ y) ∧ (x ≤ z))) ∨ (x ≤ z)) : Bool


***
          x:Bool  y:Bool  z:Bool
------------------------------------------   ∨ ∧ distributivity
(x ∨ (y ∧ z)) = ((x ∨ y) ∧ (x ∨ z)) : Bool
"""
