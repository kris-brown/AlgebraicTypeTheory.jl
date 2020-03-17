module Preorder
export preorder
using AlgebraicTypeTheory.GraphTerm: Sort, Var, App, OpDecl, SortDecl, Term, Rule, Theory, render

obdecl = SortDecl(:ob, "Underlying set of preorder")
A,B,C = [Var(x,Sort(:ob)) for x in [:A,:B,:C]]
leqdecl = SortDecl(:leq,"({}≤{})",[A,B],"A relation from A -> B")
aa,ab,bc,ac = [Sort(:leq,[x,y]) for (x,y) in [A=>A,A=>B,B=>C,A=>C]]
p,q,r = [Var(x,y) for (x,y) in [:p=>ab,:q=>bc,:r=>ab]]
refl = OpDecl(:refl,"{}ᵣ",aa,[A],"Reflexivity")
trans = OpDecl(:trans,"({}⪯{})",ac,[p,q],"Transitivity")
singl = Rule("Singleton","The sort A->B is a singleton set.",p,r,)
preorder=Theory([obdecl,leqdecl],[refl,trans],[singl],"Preorder")
print(render(preorder))
end

"""
####################################
# ******* Theory: Preorder ******* #
####################################

2 sorts, 2 ops, 0 rules

#########
# Sorts #
#########

==================================================

--------   ob
ob  sort

Underlying set of preorder


==================================================
  A,B:ob
-----------   leq
(A≤B)  sort

A relation from A -> B


##############
# Operations #
##############

==================================================
q:(B≤C)  p:(A≤B)  A,B,C:ob
--------------------------   trans
      (p⪯q) : (A≤C)

Transitivity


==================================================
   A:ob
----------   refl
Aᵣ : (A≤A)

Reflexivity

###################
# Equality Axioms #
###################

==================================================
p,r:(A≤B)  A,B:ob
-----------------   Singleton
 p = r   : (A≤B)

The sort A->B is a singleton set.


"""