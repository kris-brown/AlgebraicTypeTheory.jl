export cwf

using AlgebraicTypeTheory: SortOp, Sort, TermOp, Var, OpDecl, SortDecl, App, EqDecl, mkTheory, Judgment,render


ctx, siz, Hom = [SortOp(x,i) for (x,i) in zip([:Ctx,:size, :Hom],[0,0,"({}→{})"])]
Ctx,Size = map(Sort,[ctx,siz])
α,β,θ,A,B,C,D,Γ,Δ,Ξ = [Var(x,Ctx) for x in [:α,:β,:θ,:A,:B,:C,:D,:Γ,:Δ,:Ξ]]

Hom_aa,Hom_bb,Hom_ab,Hom_bc,Hom_ac,Hom_cd,Hom_αα,Hom_ββ,Hom_αβ,Hom_αθ,Hom_βθ,Hom_ΔΓ,HomΞΔ = [Sort(Hom, x) for x in [ [A,A],[B,B],[A,B],[B,C],[A,C],[C,D],[α,α],[β,β],[α,β],[α,θ],[β,θ],[Δ,Γ],[Ξ,Δ]]]

ctxdecl = SortDecl(Ctx,"Ctxjects of a category are a convenience to make it easier to talk about morphisms.")
homdecl = SortDecl(Hom_αβ, [α,β], "Hom-set, a set of morphisms which exists between any pair of ctxjects in a category.")
id = TermOp(:id,1)
iddecl = OpDecl(id, Hom_αα, [α], "The identity operation picks out a particular morphism in Hom(α,α) which satisfies the identity laws.")
Cmp = TermOp(:⋅,"binary")
Cmpdecl = OpDecl(Cmp,Hom_αθ,[Hom_αβ,Hom_βθ], "Composition, only defined for pairs of morphisms that match head-to-tail, is an associative operation which picks out a third.")
f,g,h,γ,δ = [Var(x,h) for (x,h) in zip([:f,:g,:h,:γ,:δ],[Hom_ab,Hom_bc,Hom_cd,Hom_ΔΓ,HomΞΔ])]
fg, gh = [App(Cmp,x) for x in [[f,g],[g,h]]]
idA,idB,idΓ = [App(id,[x]) for x in [A,B,Γ]]
f_gh, fg_h = [App(Cmp,x) for x in [[fg,h],[f,gh]]]

idldecl = EqDecl("⋅ left-identity", App(Cmp,[idA,f]), f)
idrdecl = EqDecl("⋅ right-identity", App(Cmp,[f,idB]), f)
ascdecl = EqDecl("⋅ associativity", f_gh, fg_h)

Emp = TermOp(:emp,"⋅")
empdecl = OpDecl(Emp,Ctx,"The category ctx has a terminal object")
emp = App(Emp)
Trm = TermOp(:empsubst,"!({})")
termsort = Sort(Hom,[Γ,emp])
termΓ = App(Trm,[Γ])
anyTermΓ = Var(:η,termsort)
termdecl=OpDecl(Trm,termsort,[Γ])
termundecl = EqDecl("! unique",termΓ, anyTermΓ, "The terminal morphism is unique")

sizedecl = SortDecl(Size,"Data is ordered by its size")
zero,one = [TermOp(Symbol(x),x) for x in ["0", "1"]]
One = App(one)
small, large = [OpDecl(x,Size) for x in [zero, one]]
ord = SortOp(:≦,"binary")
i,j,k = [Var(x,Size) for x in [:i,:j,:k]]
ii,ij,jk,ik,i1,ki = [Sort(ord,x) for x in
    [[i,i], [i,j], [j,k], [i,k],[i,One],[k,i]]]
orddec = SortDecl(ij,[i,j])
vii,p,q,r,s = [Var(x,y) for (x,y) in zip([:m,:p,:q,:r,:s],[ii,ij,ij,jk,ik])]

ordunidecl = EqDecl("Ord unique",p,q,"The sort i≦j is a singleton")
sizerefl = TermOp(:★i,"{}")
sizerefldec = OpDecl(sizerefl, ii,[i], "≦ reflexivity")
sizetran = TermOp(:★t,2)
OneRefl = App(sizerefl,[One])
sizetrandec = OpDecl(sizetran,ik,[p,Var(:r,jk)],"≦ transitivity")
sizemax = TermOp(:★m,1)
sizemaxdec = OpDecl(sizemax,i1,[i],"Everything is less than 1")
sizemaxdec2=EqDecl("1 max",i,One,"One is bigger than everything",[Var(:p,ki)])

Ty = SortOp(:Ty, "Ty{}({})")
TyΓi,TyΔj = [Sort(Ty, [i,Γ]), Sort(Ty,[j,Δ])]

Tydecl = SortDecl(TyΓi, [i,Γ], "Size lifting action?Presheaf Γ×sizeᵒᵖ")

AyΓi, ByΔj = [Var(:A, TyΓi), Var(:B,TyΔj)]
Tyact = TermOp(:Tyact,"({}[{}]{})")
Tyactdecl = OpDecl(Tyact,TyΔj,[AyΓi, γ, p], "Substitution action")

tyfunc1decl = EqDecl("Ty functorality 1",AyΓi,App(Tyact,[AyΓi,idΓ,vii]),
                     "functorality of Ty rule 1")

t2t1 = App(Tyact,[AyΓi,App(Cmp,[δ,γ]),s])
t2t2_ = App(Tyact,[AyΓi,γ,p])
t2t2 = App(Tyact,[t2t2_,δ,r])
var = Var(:Z,Sort(Ty,[j,Δ]))
# The Tyact prototypical i is getting bound to i in the inner
# and to j in the outer. How to deal with this? Need big change.

tyfunc2decl = EqDecl("Ty functorality 2", t2t1,t2t2,
                     "functorality of Ty rule 2",[p,r])



El = SortOp(:el, "𝐄𝐥({} ⊢ {})")
AyΓ1 = Var(:A, Sort(Ty, [One,Γ]))
elΓA = Sort(El,[Γ,AyΓ1])
Eldecl = SortDecl(elΓA, [Γ, AyΓ1])
Elact = TermOp(:Elact,"{}[{}]")
M = Var(:M,elΓA)

Aγ1 = App(Tyact,[AyΓ1,γ,OneRefl])
Elactdecl = OpDecl(Elact,Aγ1,[M,γ])

eliddecl=EqDecl("Elact id",App(Elact,[M,idΓ]),M)


cwf = mkTheory("cwf", Judgment[ctxdecl, homdecl, iddecl, Cmpdecl, idldecl, idrdecl, ascdecl, empdecl, termdecl, termundecl,
sizedecl,small,large,orddec,ordunidecl,sizerefldec,sizetrandec,sizemaxdec,sizemaxdec2,Tydecl, Tyactdecl, tyfunc1decl,tyfunc2decl,Eldecl,Elactdecl], true)

"""
Rendered theory

###############################
# ******* Theory: cwf ******* #
###############################

#########
# Sorts #
#########

***
i:size  Γ:Ctx
-------------   Ty
Tyi(Γ)  sort

Size lifting action?Presheaf Γ×sizeᵒᵖ


***
α:Ctx  β:Ctx
------------   Hom
(α→β)  sort

Hom-set, a set of morphisms which exists between any pair of ctxjects in a category.


***
A:Ty1(Γ)  Γ:Ctx
---------------   el
𝐄𝐥(Γ ⊢ A)  sort


***

----------   size
size  sort

Data is ordered by its size


***
i:size  j:size
--------------   ≦
(i ≦ j)  sort


***

---------   Ctx
Ctx  sort

Ctxjects of a category are a convenience to make it easier to talk about morphisms.


##############
# Operations #
##############

***

--------   1
1 : size


***

-------   emp
⋅ : Ctx

The category ctx has a terminal object


***
    i:size
---------------   ★m
★m(i) : (i ≦ 1)

Everything is less than 1


***
A:Tyi(Γ) i:size j:size p:(i ≦ j) Γ:Ctx Δ:Ctx γ:(Δ→Γ)
----------------------------------------------------   Tyact
                  (A[γ]p) : Tyj(Δ)

Substitution action


***
    α:Ctx
-------------   id
id(α) : (α→α)

The identity operation picks out a particular morphism in Hom(α,α) which satisfies the identity laws.


***
  i:size
-----------   ★i
i : (i ≦ i)

≦ reflexivity


***
A:Ty1(Γ) M:𝐄𝐥(Γ ⊢ A) Γ:Ctx Δ:Ctx γ:(Δ→Γ)
----------------------------------------   Elact
             M[γ] : (A[γ]1)


***
i:size j:size k:size p:(i ≦ j) r:(j ≦ k)
----------------------------------------   ★t
           ★t(p,r) : (i ≦ k)

≦ transitivity


***
   Γ:Ctx
------------   empsubst
!(Γ) : (Γ→⋅)


***
   α:Ctx β:Ctx θ:Ctx
-----------------------   ⋅
((α→β) ⋅ (β→θ)) : (α→θ)

Composition, only defined for pairs of morphisms that match head-to-tail, is an associative operation which picks out a third.


***

--------   0
0 : size


###################
# Equality Axioms #
###################

***
A:Tyi(Γ)  i:size  m:(i ≦ i)  Γ:Ctx
----------------------------------   Ty functorality 1
     A = (A[id(Γ)]m) : Tyi(Γ)

functorality of Ty rule 1


***
i:size  k:size  p:(k ≦ i)
-------------------------   1 max
      i = 1 : size

One is bigger than everything


***
 A:Ctx  B:Ctx  f:(A→B)
-----------------------   ⋅ right-identity
(f ⋅ id(B)) = f : (A→B)


***
 A:Ctx  B:Ctx  f:(A→B)
-----------------------   ⋅ left-identity
(id(A) ⋅ f) = f : (A→B)


***
A:Tyi(Γ)  i:size  j:size  k:size  p:(i ≦ j)  r:(j ≦ k)  s:(i ≦ k)  Γ:Ctx  Δ:Ctx  Ξ:Ctx  γ:(Δ→Γ)  δ:(Ξ→Δ)
--------------------------------------------------------------------------------------------------------   Ty functorality 2
                                 (A[(δ ⋅ γ)]s) = ((A[γ]p)[δ]r) : Tyk(Ξ)

functorality of Ty rule 2


***
A:Ctx  B:Ctx  C:Ctx  D:Ctx  f:(A→B)  g:(B→C)  h:(C→D)
-----------------------------------------------------   ⋅ associativity
        ((f ⋅ g) ⋅ h) = (f ⋅ (g ⋅ h)) : (A→D)


***
 Γ:Ctx  η:(Γ→⋅)
----------------   ! unique
!(Γ) = η : (Γ→⋅)

The terminal morphism is unique


***
i:size  j:size  p:(i ≦ j)  q:(i ≦ j)
------------------------------------   Ord unique
          p = q : (i ≦ j)

The sort i≦j is a singleton

"""
