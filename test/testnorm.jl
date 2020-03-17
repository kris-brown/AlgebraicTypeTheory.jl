using Test
using AlgebraicTypeTheory.Graph
using AlgebraicTypeTheory.GraphTerm
using AlgebraicTypeTheory.Theories.Monoid:monoid
using AlgebraicTypeTheory.Theories.Cat:cat
using MetaGraphs
"""
Tests for the normalization of terms by repeatedly applying rewrite rules
"""
# ##########################################################################################
# Normalization in Monoid
X,Y,Z,A,B,C,D = [Var(x, Sort(:Ob)) for x in [:X,:Y,:Z,:A,:B,:C,:D]]
id = App(:e)

xyzx = infer(monoid, App(:*,[X,App(:*,[Y,App(:*,[Z,X])])]))
# (X * (Y * (Z * X)))

_xyz_x = infer(monoid,
    App(:*, [
        App(:*, [
            App(:*, [
                App(:*, [
                    App(:*,[
                            id,
                            X]),
                        Y]),
                    Z]),
            id]),
        X]))
# (((((e() * X) * Y) * Z) * e()) * X)
@test normalize(monoid,_xyz_x) == xyzx

# ##########################################################################################
# Normalization in Cat
Hom_ab,Hom_bc,Hom_ac,Hom_cd = [Sort(:Hom, x)
    for x in [ [A,B],[B,C],[A,C],[C,D]]]
ab,bc,ac,cd = [Var(x,h) for (x,h) in zip([:ab,:bc,:ac,:cd],
    [Hom_ab,Hom_bc,Hom_ac,Hom_cd])]
aa, cc = [App(:id,[x]) for x in [A,C]]

abcd = infer(cat,App(:cmp,[App(:cmp,[ab,bc]),cd]))
# ((ab ⋅ bc) ⋅ cd)

aa__abbc_cc = App(:cmp,[aa,
    App(:cmp,[App(:cmp,[ab,bc]),cc])])
cccccd = App(:cmp,[cc, App(:cmp,[cc,cd])])
a_b_c_d = infer(cat,App(:cmp, [aa__abbc_cc,cccccd]))
# ((id(A) ⋅ ((ab ⋅ bc) ⋅ id(C))) ⋅ (id(C) ⋅ (id(C) ⋅ cd)))
@test abcd == normalize(cat, a_b_c_d)

##########################################################################################

