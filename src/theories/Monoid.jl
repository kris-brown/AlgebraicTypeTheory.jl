module Monoid

if isdefined(@__MODULE__, :LanguageServer)
    include("../DataTypes.jl")
    include("../Core.jl")
    using .DataTypes
else
    using DataTypes
end


ob = SortOp(:Ob)
Ob = Sort(ob)
obdecl = SortDecl(Ob, "Underlying set of a monoid")

eOp = TermOp(:e)
m_id = OpDecl(eOp, Ob, "Identity element of monoid")

Mul = TermOp(:mul, "({} * {})")
mul = OpDecl(Mul, Ob, [Var(:α, Ob), Var(:β, Ob)])
X, Y, Z = [Var(x, Ob) for x in [:X,:Y,:Z]]

id_term = App(eOp)

m_idl = EqDecl("mul left-identity", X, App(Mul, [id_term, X]))
m_idr = EqDecl("mul right-identity", X, App(Mul, [X, id_term]))

m_asc = EqDecl("mul associativity",
    App(Mul, [X,App(Mul, [Y,Z])]),App(Mul, [App(Mul, [X,Y]),Z]))

# monoid = mkTheory("Monoid", Judgment[obdecl, mul, m_id, m_idl, m_idr, m_asc])

end
"""
Rendered theory:

##################################
# ******* Theory: Monoid ******* #
##################################

#########
# Sorts #
#########

***

--------   ob
ob  sort

Underlying set of a monoid


##############
# Operations #
##############

***

------   e
e : ob

Identity element of monoid


***
 α:ob β:ob
------------   mul
(α * β) : ob


###################
# Equality Axioms #
###################

***
      X:ob
----------------   mul right-identity
X = (X * e) : ob


***
         X:ob  Y:ob  Z:ob
----------------------------------   mul associativity
(X * (Y * Z)) = ((X * Y) * Z) : ob


***
      X:ob
----------------   mul left-identity
X = (e * X) : ob
"""
