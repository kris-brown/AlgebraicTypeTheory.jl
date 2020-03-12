# using AlgebraicTypeTheory
# using AlgebraicTypeTheory.Theories: monoid, Mul, Ob, eOp, cat, Hom, Cmp, id, cwf, cwf,compcomp

# ##########################################################################################
# cr = x -> print(render(cwf,x))

# X,Y,Z,A,B,C,D = [Var(x, Ob) for x in [:X,:Y,:Z,:A,:B,:C,:D]]
# id_term = App(eOp)
# eqs = collect(monoid.eqs)
# @test render(monoid) isa String



# d1, d2 = map(degrade, [eqs[1].t1,eqs[1].t2])


# t1, t2 = [buildTerm(monoid,x) for x in [d1,d2]]
# @test t1 == t2

# _xyz_x = App(Mul, [
#         App(Mul, [
#             App(Mul, [
#                 App(Mul, [
#                     App(Mul,[
#                             id_term,
#                             X]),
#                         Y]),
#                     Z]),
#             id_term]),
#             X])

# xyz_x = App(Mul, [
#             X
#             App(Mul, [
#                 Y,
#                 App(Mul, [
#                         Z,
#                         App(Mul,[
#                             id_term,
#                             X])
#                         ])
#                     ])
#             ])
# x1, x2 = [buildTerm(monoid, x) for x in [_xyz_x, xyz_x]]
# @test x1 == x2
# ##########################################################################################
# Hom_ab,Hom_bc,Hom_ac,Hom_cd = [Sort(Hom, x)
#     for x in [ [A,B],[B,C],[A,C],[C,D]]]
# ab,bc,ac,cd = [Var(x,h) for (x,h) in zip([:ab,:bc,:ac,:cd],
#     [Hom_ab,Hom_bc,Hom_ac,Hom_cd])]
# aa, cc = [App(id,[x]) for x in [A,C]]
# abcd = buildTerm(cat,App(Cmp,[App(Cmp,[ab,bc]),cd]))
# aa__abbc_cc = App(Cmp,[aa,
#     App(Cmp,[App(Cmp,[ab,bc]),cc])])
# cccccd = App(Cmp,[cc, App(Cmp,[cc,cd])])
# a_b_c_d = buildTerm(cat,App(Cmp, [aa__abbc_cc,cccccd]))
# @test abcd == a_b_c_d
# ##########################################################################################


# # THINGS TO SHOW
#     # if you try to define an op e.g. id X=>X with zero args, then it fails b/c
#     # there is no way to identify X
