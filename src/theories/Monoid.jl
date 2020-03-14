module Monoid
export monoid
using GraphTerm: Sort, Var, App, OpDecl, SortDecl, Term, Rule, Theory, render

Ob = Sort(:Ob)
obdecl = SortDecl(:Ob, "Underlying set of a monoid")

m_id = OpDecl(:e, 0, Ob, Term[], "Identity element of monoid")

mul = OpDecl(:*, "binary", Ob, [Var(:α, Ob), Var(:β, Ob)], "Multiplication")
X, Y, Z = [Var(x, Ob) for x in [:X,:Y,:Z]]

id_term = App(:e)

m_idl = Rule("mul left-identity", X, App(:*, [id_term, X]))
m_idr = Rule("mul right-identity", X, App(:*, [X, id_term]))

m_asc = Rule("mul associativity",
    App(:*, [X,App(:*, [Y,Z])]),App(:*, [App(:*, [X,Y]),Z]))

monoid = Theory([obdecl], [mul,m_id],[m_idl, m_idr, m_asc],"Monoid")
print(render(monoid))
end

"""
##################################
# ******* Theory: Monoid ******* #
##################################

1 sorts, 2 ops, 3 rules

#########
# Sorts #
#########

==================================================

--------   Ob
Ob  sort

Underlying set of a monoid


##############
# Operations #
##############

==================================================
   α,β:Ob
------------   *
(α * β) : Ob

Multiplication


==================================================

--------   e
e() : Ob

Identity element of monoid


###################
# Equality Axioms #
###################

==================================================
              X,Y,Z:Ob
------------------------------------   mul associativity
(X * (Y * Z)) = ((X * Y) * Z)   : Ob


==================================================
        X:Ob
--------------------   mul left-identity
X = (e() * X)   : Ob


==================================================
        X:Ob
--------------------   mul right-identity
X = (X * e())   : Ob
"""