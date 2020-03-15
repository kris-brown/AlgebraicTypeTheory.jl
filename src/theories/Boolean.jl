module Boolean
export boolalg
using AlgebraicTypeTheory.GraphTerm: Sort, Var, App, OpDecl, SortDecl, Term, Rule, Theory, render

bool = Sort(:Bool)
booldec = SortDecl(:Bool, "The underlying set of a boolean algebra")

bX, bY, bZ, bα, bβ = [Var(x, bool) for x in [:x, :y, :z,:α,:β]]

topdecl = OpDecl(:⊤, 0,bool, Term[],"Top element, x ∨ ¬x")
botdecl = OpDecl(:⊥, 0, bool, Term[],"Bottom element, x ∧ ¬x")
negdec = OpDecl(:¬, 1, bool, [bX], "Negation/complement")

landdec = OpDecl(:∧, "binary",bool, [bα,bβ], "Meet/Greatest lower bound")
lordec = OpDecl(:∨, "binary",bool, [bα,bβ], "Join/Least upper bound")

absand, absor = [Rule("$op1, $op2 absorption", bX,
App(op1, [bX, App(op2, [bX, bY])])) for (op1, op2) in [[:∧, :∨], [:∨,:∧]]]

idenand, idenor = [Rule( "$op1 identity", bX,
    App(op1, [bX, App(op2)])) for (op1, op2) in [[:∧,:⊤], [:∨,:⊥]]]

symand, symor = [Rule("$op symmetry", App(op, [bX,bY]), App(op, [bY,bX]))
             for op in [:∧, :∨]]

ascand, ascor = [Rule("$op associativity",
App(op, [bX,App(op, [bY,bZ])]),App(op, [App(op, [bX,bY]),bZ]))
for op in [:∧, :∨]]

distand, distor = [Rule("$op1 $op2 distributivity",
    App(op1, [bX,App(op2, [bY,bZ])]),
    App(op2, [App(op1, [bX,bY]),App(op1, [bX,bZ])]))
    for (op1, op2) in [[:∧, :∨], [:∨,:∧]]]

topdef, botdef = [Rule("$op def",App(op),App(o2,[bX,App(:¬,[bX])])) for
    (op,o2) in [(:⊤,:∨),(:⊥,:∧)]]

boolalg = Theory([booldec], [negdec, landdec, lordec, topdecl, botdecl],
                 [symand, symor, ascand, ascor, idenand, idenor, absand,
                  absor,distand, distor,topdef, botdef],"BooleanAlgebra")
# print(render(boolalg))
end
"""


##########################################
# ******* Theory: BooleanAlgebra ******* #
##########################################

1 sorts, 5 ops, 12 rules

#########
# Sorts #
#########

==================================================

----------   Bool
Bool  sort

The underlying set of a boolean algebra


##############
# Operations #
##############

==================================================

----------   ⊤
⊤() : Bool

Top element, x ∨ ¬x


==================================================
   α,β:Bool
--------------   ∨
(α ∨ β) : Bool

Join/Least upper bound


==================================================
   α,β:Bool
--------------   ∧
(α ∧ β) : Bool

Meet/Greatest lower bound


==================================================
  x:Bool
-----------   ¬
¬(x) : Bool

Negation/complement


==================================================

----------   ⊥
⊥() : Bool

Bottom element, x ∧ ¬x


###################
# Equality Axioms #
###################

==================================================
              x,y,z:Bool
--------------------------------------   ∧ associativity
(x ∧ (y ∧ z)) = ((x ∧ y) ∧ z)   : Bool


==================================================
        x:Bool
----------------------   ∧ identity
x = (x ∧ ⊤())   : Bool


==================================================
         x,y:Bool
--------------------------   ∧ symmetry
(x ∧ y) = (y ∧ x)   : Bool


==================================================
                 x,y,z:Bool
--------------------------------------------   ∧ ∨ distributivity
(x ∧ (y ∨ z)) = ((x ∧ y) ∨ (x ∧ z))   : Bool


==================================================
         x,y:Bool
--------------------------   ∧, ∨ absorption
x = (x ∧ (x ∨ y))   : Bool


==================================================
              x,y,z:Bool
--------------------------------------   ∨ associativity
(x ∨ (y ∨ z)) = ((x ∨ y) ∨ z)   : Bool


==================================================
        x:Bool
----------------------   ∨ identity
x = (x ∨ ⊥())   : Bool


==================================================
         x,y:Bool
--------------------------   ∨ symmetry
(x ∨ y) = (y ∨ x)   : Bool


==================================================
                 x,y,z:Bool
--------------------------------------------   ∨ ∧ distributivity
(x ∨ (y ∧ z)) = ((x ∨ y) ∧ (x ∨ z))   : Bool


==================================================
         x,y:Bool
--------------------------   ∨, ∧ absorption
x = (x ∨ (x ∧ y))   : Bool


==================================================
         x:Bool
-------------------------   ⊤ def
⊤() = (x ∨ ¬(x))   : Bool


==================================================
         x:Bool
-------------------------   ⊥ def
⊥() = (x ∧ ¬(x))   : Bool
"""