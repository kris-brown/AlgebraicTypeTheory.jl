module Cwf_no_level
using AlgebraicTypeTheory.GraphTerm: Sort, Var, App, OpDecl, SortDecl, Term, Rule, Theory, render, extend, infer, viz

#############
# CONTEXTS #
############
Ctx, Size = map(Sort, [:Ctx, :Size])
A, B, C, D, Γ, Δ, Ξ = [Var(x, Ctx) for x in [:A,:B,:C,:D,:Γ,:Δ,:Ξ]]
Hom_aa, Hom_bb, Hom_ab, Hom_bc, Hom_ac, Hom_cd, Hom_ΔΓ, HomΞΔ = [Sort(:Hom, x) for x in [ [A,A],[B,B],[A,B],[B,C],[A,C],[C,D],[Δ,Γ],[Ξ,Δ]]]
f, g, h, γ, δ = [Var(x, h) for (x, h) in zip([:f,:g,:h,:γ,:δ], [Hom_ab,Hom_bc,Hom_cd,Hom_ΔΓ,HomΞΔ])]
ctxdecl = SortDecl(:Ctx, """Contexts: Concretely, a mapping xᵢ:Xᵢ of free variables to types.
Consider these as objects in a category C.""")
homdecl = SortDecl(:Hom, "{}→{}", [A,B], "Substitutions between contexts: concretely, a substitution bᵢ:βᵢ↦aᵢ:αᵢ.
Consider these as morphisms in the category C.")
iddecl = OpDecl(:id, 1, Hom_aa, [A], "The identity morphism")

cmpdecl = OpDecl(:cmp, "({}⋅{})", Hom_ac, [f,g], "Composition, only defined for pairs of morphisms that match head-to-tail, is an associative operation which picks out a third.")

idA, idB, idΓ = [App(:id, [x]) for x in [A,B,Γ]]
fg, gh = [App(:cmp, x) for x in [[f,g],[g,h]]]

f_gh, fg_h = [App(:cmp, x) for x in [[fg,h],[f,gh]]]

idldecl = Rule("⋅ left-identity", f, App(:cmp, [idA,f]))
idrdecl = Rule("⋅ right-identity", f, App(:cmp, [f,idB]))
ascdecl = Rule("⋅ associativity", f_gh, fg_h)

cwf = Theory([ctxdecl,homdecl], [iddecl,cmpdecl], [idldecl,idrdecl,ascdecl], "cwf1")
####################
# TERMINAL CONTEXT #
####################

empdecl = OpDecl(:emp, "⋅", Ctx, "The category C has a terminal object: the empty context")
emp = App(:emp)
termsort = Sort(:Hom, [Γ,emp])
termΓ = App(:empsubst, [Γ])
termdecl = OpDecl(:empsubst, "!({})", termsort, [Γ], "Substitution into an empty context ")

anyTermΓ = Var(:η, termsort)
termundecl = Rule("! unique", "Substitution into an empty context is unique.", termΓ, anyTermΓ, )

cwf = extend(cwf, [], [empdecl,termdecl], [termundecl], "cwf2")

######################
# TYPES AND ELEMENTS #
######################
Tydecl = SortDecl(:Ty, "Ty({})", [Γ], "The sort of types in context Γ")
TyΓ, TyΔ = [Sort(:Ty, [Γ]), Sort(:Ty, [Δ])]
TyΓ = Sort(:Ty, [Γ])
AyΓ = Var(:A, TyΓ)
elΓA = Sort(:el, [Γ,AyΓ])
Eldecl = SortDecl(:el, "𝐄𝐥({}⊢{})", [Γ, AyΓ], "The sort of terms of type A (in ctx Γ), where A is of size α
 'This is to fix a dependent presheaf El: Psh(ctx)/Ty, i.e. a nat. trans. π: El→Ty'")

Tyactdecl = OpDecl(:Tyact, "{}[{}]",TyΔ,[AyΓ, γ],
        "Substitution action: apply the substitution γ (of type Δ→Γ) to a some type A (in ctx Γ) to obtain a term of type Δ")


tyfunc1decl = Rule("Ty identity", "Applying the identity substitution (on ctx Γ) to a type in ctx Γ yields the same type", AyΓ, App(:Tyact, [AyΓ,idΓ]))

δγ = App(:cmp, [δ,γ])
t2t1 = App(:Tyact, [AyΓ,δγ])
AyΓγ = App(:Tyact, [AyΓ,γ])
t2t2 = App(:Tyact, [AyΓγ,δ])

tyfunc2decl = Rule("Ty preserves composition", """The functor to Fam from C preserves composition of substitutions:
applying two substitutions in sequence is the same as applying the composition of the substitutions in C""",
t2t1,t2t2)


a = Var(:a, elΓA)
ElΔAγ = Sort(:el, [Δ,AyΓγ])

Elactdecl = OpDecl(:Elact, "{}[{}]",ElΔAγ,[a,γ], """
    Substitution action: apply the substitution γ (of type Δ→Γ) to a term of type A (in ctx Γ)
    Result: a term of type A[γ] (in ctx Δ)""")

elid2 = App(:Elact, [a,idΓ])
eliddecl = Rule("Term substitution identity",
    "The identity substitution on a term yields the same term", a, elid2)

elcompdecl = Rule("Term substitution composition","""
    The functor to Fam from C preserves composition of substitutions:
    Applying two substitutions in sequence is the same as applying the composition of the substitutions in C""",
    App(:Elact, [a,δγ]), App(:Elact, [App(:Elact, [a,γ]),δ]))

cwf = extend(cwf, [Tydecl,Eldecl], [Tyactdecl,Elactdecl], [tyfunc1decl,tyfunc2decl, eliddecl, elcompdecl], "cwf4")



# #########################
# # CONTEXT COMPREHENSION #
# #########################
ΓA = App(:ext, [Γ,AyΓ])
ctxcmpdecl = OpDecl(:ext, "({}.{})", Ctx,[Γ,AyΓ],
                    "Context compreshension operation")
N = Var(:N, ElΔAγ)
snocdecl = OpDecl(:snoc, "⟨{},{}⟩", Sort(:Hom, [Δ,ΓA]), [γ,N], "???")
Pdecl = OpDecl(:p, "𝐩({})", Sort(:Hom, [ΓA,Γ]), [AyΓ], "Projection function 'drop'???")
P = App(:p, [AyΓ])
TyAp = App(:Tyact, [AyΓ,P])
Qdecl = OpDecl(:q, "𝐪({})", Sort(:el, [ΓA,TyAp]), [AyΓ], "Projection function 'var'???")
Q = App(:q, [AyΓ])
peq = Rule("Universal property of 𝐩", γ, App(:cmp, [App(:snoc, [γ,N]),P]))
qeq = Rule("Universal property of 𝐪", N, App(:Elact, [Q,App(:snoc, [γ,N])]))
pqeq = Rule("𝐩𝐪 property", App(:id, [ΓA]), App(:snoc, [P,Q]))
cct1 = App(:cmp, [δ,App(:snoc, [γ,N])])
cct2 = App(:snoc, [App(:cmp, [δ,γ]), App(:Elact, [N,δ])])
compcomp = Rule("Comp comp", cct1, cct2)

cwf = extend(cwf, [], [ctxcmpdecl,snocdecl,Pdecl,Qdecl], [peq,qeq,pqeq,compcomp], "cwf5")

##############################
# Type theoretic connectives #
##############################
B = Var(:B, Sort(:Ty, [ΓA]))
pidecl = OpDecl(:Pi, "Π({},{})", TyΓ, [AyΓ,B], "Π formation")

ΠAB = App(:Pi, [AyΓ,B])
lamsort = Sort(:el, [Γ,ΠAB])
M = Var(:M, Sort(:el, [ΓA,B]))
lamM = App(:lam,[M])
lamdecl = OpDecl(:lam, "λ({})", lamsort, [M], "Π introduction")


pisub22 = App(:Tyact,[B,App(:snoc,[App(:cmp,[P,γ]),Q])])
pisub2 = App(:Pi,[AyΓγ, pisub22])
pisubdecl = Rule("Pi substitution", App(:Tyact,[ΠAB,γ]), pisub2)

elactλ = App(:Elact,[lamM, γ])
yopq = App(:snoc,[App(:cmp,[P,γ]),Q])
elact_yopq = App(:Elact,[M,yopq])
lamsubdecl = Rule("Lambda Substitution",elactλ,elact_yopq)

MM = Var(:M,Sort(:el,[Γ,ΠAB]))
NN = Var(:N,Sort(:el,[Γ,App(:Tyact,[AyΓ,idΓ])]))

# TO MOVE ON, WE NEED TO INCORPORATE SUBSTITUTIONS (DEFINED UP TO THIS PT IN TIME)
# IN THE TYPE INFERENCE PROCESS.
# Because A[id] == A we should be able to do stuff with A[id] in the place of A, like El(Γ,A[id])
# Currently using a hack.

snocNN=App(:snoc,[idΓ,NN])

apps2 = App(:Tyact, [B, apps22])
appsort = Sort(:el,[Γ, apps2])
appdecl = OpDecl(:app,"𝐚𝐩𝐩({},{})",appsort,[MM,NN], "Pi elimination via application")
appMN = App(:app,[MM,NN])

# WE ARE MISSING AppSubstitution,PiUnicity,PiComputation
cwf = cwf_no_level = extend(cwf, [], [pidecl, lamdecl, appdecl], [pisubdecl,lamsubdecl], "cwf7")
# print(render(cwf))


"""
##############################################################################
Testing area
##############################################################################
"""
# the args individually work but not ad2. Even when replacing NN w/ a version without the id
NN_ = Var(:N,Sort(:el,[Γ,AyΓ]))
ad2 = App(:app,[App(:Elact,[MM,γ]),App(:Elact,[NN_,γ])])
appsdecl = Rule("App substitution",App(:Elact,[appMN,γ]),ad2)
#####
piu = App(:app,[App(:Elact,[MM,P]),Q])
# piu cannot be inferred
piudecl = Rule("Pi Unicity",MM,[App(:lam,piu)])
######
# this term cannot be inferred
pi2=App(:Elact,[MM,snocNN])
picdecl = Rule("Pi computation",appMN,pi2)

end
"""

################################
# ******* Theory: cwf7 ******* #
################################

4 sorts, 13 ops, 14 rules

#########
# Sorts #
#########

==================================================

---------   Ctx
Ctx  sort

Contexts: Concretely, a mapping xᵢ:Xᵢ of free variables to types.
Consider these as objects in a category C.


==================================================
   Γ:Ctx
-----------   Ty
Ty(Γ)  sort

The sort of types in context Γ


==================================================
 A,B:Ctx
---------   Hom
A→B  sort

Substitutions between contexts: concretely, a substitution bᵢ:βᵢ↦aᵢ:αᵢ.
Consider these as morphisms in the category C.


==================================================
A:Ty(Γ)  Γ:Ctx
--------------   el
𝐄𝐥(Γ⊢A)  sort

The sort of terms of type A (in ctx Γ), where A is of size α
 'This is to fix a dependent presheaf El: Psh(ctx)/Ty, i.e. a nat. trans. π: El→Ty'


##############
# Operations #
##############

==================================================
A:Ty(Γ)  Γ:Ctx
--------------   ext
 (Γ.A) : Ctx

Context compreshension operation


==================================================
B:Ty((Γ.A))  A:Ty(Γ)  Γ:Ctx
---------------------------   Pi
      Π(A,B) : Ty(Γ)

Π formation


==================================================
   A:Ctx
-----------   id
id(A) : A→A

The identity morphism


==================================================
γ:Δ→Γ  A:Ty(Γ)  Γ,Δ:Ctx
-----------------------   Tyact
     A[γ] : Ty(Δ)

Substitution action: apply the substitution γ (of type Δ→Γ) to a some type A (in ctx Γ) to obtain a term of type Δ


==================================================

-------   emp
⋅ : Ctx

The category C has a terminal object: the empty context


==================================================
γ:Δ→Γ  A:Ty(Γ)  Γ,Δ:Ctx  a:𝐄𝐥(Γ⊢A)
----------------------------------   Elact
        a[γ] : 𝐄𝐥(Δ⊢A[γ])

Substitution action: apply the substitution γ (of type Δ→Γ) to a term of type A (in ctx Γ)
Result: a term of type A[γ] (in ctx Δ)


==================================================
B:Ty((Γ.A))  A:Ty(Γ)  M:𝐄𝐥((Γ.A)⊢B)  Γ:Ctx
------------------------------------------   lam
           λ(M) : 𝐄𝐥(Γ⊢Π(A,B))

Π introduction


==================================================
γ:Δ→Γ  A:Ty(Γ)  N:𝐄𝐥(Δ⊢A[γ])  Γ,Δ:Ctx
-------------------------------------   snoc
           ⟨γ,N⟩ : Δ→(Γ.A)

???


==================================================
B:Ty((Γ.A))  A:Ty(Γ)  M:𝐄𝐥(Γ⊢Π(A,B))  N:𝐄𝐥(Γ⊢A[id(Γ)])  Γ:Ctx
-------------------------------------------------------------   app
                𝐚𝐩𝐩(M,N) : 𝐄𝐥(Γ⊢B[⟨id(Γ),N⟩])

Pi elimination via application


==================================================
f:A→B  g:B→C  A,B,C:Ctx
-----------------------   cmp
      (f⋅g) : A→C

Composition, only defined for pairs of morphisms that match head-to-tail, is an associative operation which picks out a third.


==================================================
    Γ:Ctx
--------------   empsubst
!(Γ) : Γ→emp()

Substitution into an empty context


==================================================
A:Ty(Γ)  Γ:Ctx
--------------   p
𝐩(A) : (Γ.A)→Γ

Projection function 'drop'???


==================================================
     A:Ty(Γ)  Γ:Ctx
------------------------   q
𝐪(A) : 𝐄𝐥((Γ.A)⊢A[𝐩(A)])

Projection function 'var'???


###################
# Equality Axioms #
###################

==================================================
  η:Γ→emp()  Γ:Ctx
--------------------   ! unique
!(Γ) = η   : Γ→emp()

Substitution into an empty context is unique.


==================================================
γ:Δ→Γ  A:Ty(Γ)  N:𝐄𝐥(Δ⊢A[γ])  δ:Ξ→Δ  Γ,Δ,Ξ:Ctx
----------------------------------------------   Comp comp
     (δ⋅⟨γ,N⟩) = ⟨(δ⋅γ),N[δ]⟩   : Ξ→(Γ.A)


==================================================
γ:Δ→Γ  A:Ty(Γ)  B:Ty((Γ.A))  M:𝐄𝐥((Γ.A)⊢B)  Γ,Δ:Ctx
---------------------------------------------------   Lambda Substitution
 λ(M)[γ] = M[⟨(𝐩(A)⋅γ),𝐪(A)⟩]   : 𝐄𝐥(Δ⊢Π(A,B)[γ])


==================================================
      γ:Δ→Γ  A:Ty(Γ)  B:Ty((Γ.A))  Γ,Δ:Ctx
------------------------------------------------   Pi substitution
Π(A,B)[γ] = Π(A[γ],B[⟨(𝐩(A)⋅γ),𝐪(A)⟩])   : Ty(Δ)


==================================================
γ:Δ→Γ  A:Ty(Γ)  a:𝐄𝐥(Γ⊢A)  δ:Ξ→Δ  Γ,Δ,Ξ:Ctx
-------------------------------------------   Term substitution composition
   a[(δ⋅γ)] = a[γ][δ]   : 𝐄𝐥(Ξ⊢A[(δ⋅γ)])

The functor to Fam from C preserves composition of substitutions:
Applying two substitutions in sequence is the same as applying the composition of the substitutions in C


==================================================
A:Ty(Γ)  Γ:Ctx  a:𝐄𝐥(Γ⊢A)
-------------------------   Term substitution identity
a = a[id(Γ)]   : 𝐄𝐥(Γ⊢A)

The identity substitution on a term yields the same term


==================================================
    A:Ty(Γ)  Γ:Ctx
----------------------   Ty identity
A = A[id(Γ)]   : Ty(Γ)

Applying the identity substitution (on ctx Γ) to a type in ctx Γ yields the same type


==================================================
γ:Δ→Γ  A:Ty(Γ)  δ:Ξ→Δ  Γ,Δ,Ξ:Ctx
--------------------------------   Ty preserves composition
  A[(δ⋅γ)] = A[γ][δ]   : Ty(Ξ)

The functor to Fam from C preserves composition of substitutions:
applying two substitutions in sequence is the same as applying the composition of the substitutions in C


==================================================
γ:Δ→Γ  A:Ty(Γ)  N:𝐄𝐥(Δ⊢A[γ])  Γ,Δ:Ctx
-------------------------------------   Universal property of 𝐩
      γ = (⟨γ,N⟩⋅𝐩(A))   : Δ→Γ


==================================================
γ:Δ→Γ  A:Ty(Γ)  N:𝐄𝐥(Δ⊢A[γ])  Γ,Δ:Ctx
-------------------------------------   Universal property of 𝐪
   N = 𝐪(A)[⟨γ,N⟩]   : 𝐄𝐥(Δ⊢A[γ])


==================================================
f:A→B  g:B→C  A,B,C,D:Ctx  h:C→D
--------------------------------   ⋅ associativity
 ((f⋅g)⋅h) = (f⋅(g⋅h))   : A→D


==================================================
   f:A→B  A,B:Ctx
---------------------   ⋅ left-identity
f = (id(A)⋅f)   : A→B


==================================================
   f:A→B  A,B:Ctx
---------------------   ⋅ right-identity
f = (f⋅id(B))   : A→B


==================================================
            A:Ty(Γ)  Γ:Ctx
---------------------------------------   𝐩𝐪 property
id((Γ.A)) = ⟨𝐩(A),𝐪(A)⟩   : (Γ.A)→(Γ.A)


"""