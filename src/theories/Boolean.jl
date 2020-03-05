using AlgebraicTypeTheory: SortOp, Sort, TermOp, Var, OpDecl, SortDecl, App, EqDecl,
                mkTheory, Judgment,render
export boolalg

bool = SortOp(:Bool)
Bool = Sort(bool)
booldec = SortDecl(Bool,"The underlying set of a boolean algebra")

bX, bY, bZ, bα,bβ = [Var(x, Bool) for x in [:x, :y, :z,:α,:β]]
top, bot = [TermOp(x) for x in [:⊤,:⊥]]
topdecl = OpDecl(top,Bool,"Top element, x ∨ ¬x")
botdecl = OpDecl(bot,Bool,"Bottom element, x ∧ ¬x")

neg = TermOp(:¬, 1)
negdec = OpDecl(neg, Bool, [bX])

land, lor = [TermOp(x,"binary") for x in [:∧ , :∨]]
landdec = OpDecl(land, Bool,[bα,bβ],"Meet/Greatest lower bound")
lordec = OpDecl(lor, Bool,[bα,bβ],"Join/Least upper bound")

absand, absor = [EqDecl(
    "$(op1.sym), $(op2.sym) absorption", bX,
    App(op1, [bX, App(op2, [bX, bY])])) for (op1,op2) in
    [[land,lor], [lor,land]]]

idenand, idenor = [EqDecl(
    "$(op1.sym) identity", bX,
    App(op1, [bX, App(op2)])) for (op1, op2) in
    [[land,top], [lor,bot]]]

symand, symor = [EqDecl("$op symmetry", App(op,[bX,bY]), App(op,[bY,bX]))
                 for op in [land,lor]]

ascand, ascor = [EqDecl("$op associativity",
    App(op,[bX,App(op,[bY,bZ])]),App(op,[App(op,[bX,bY]),bZ]))
    for op in [land, lor]]

distand, distor = [EqDecl("$op1 $op2 distributivity",
    App(op1,[bX,App(op2,[bY,bZ])]),
    App(op2,[App(op1,[bX,bY]),App(op1,[bX,bZ])]))
    for (op1, op2) in [[land,lor], [lor,land]]]

boolalg = mkTheory("BooleanAlgebra", Judgment[
    booldec, negdec, landdec, lordec, topdecl, botdecl, symand, symor, ascand,
    ascor, idenand, idenor, absand, absor,distand, distor])


"""
Rendered Theory

##########################################
# ******* Theory: BooleanAlgebra ******* #
##########################################

#########
# Sorts #
#########

***

----------   Bool
Bool  sort

The underlying set of a boolean algebra


##############
# Operations #
##############

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
          x:Bool  y:Bool  z:Bool
------------------------------------------   ∨ ∧ distributivity
(x ∨ (y ∧ z)) = ((x ∨ y) ∧ (x ∨ z)) : Bool

"""
