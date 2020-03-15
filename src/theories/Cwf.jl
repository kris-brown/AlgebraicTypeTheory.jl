module Cwf
export cwf
using AlgebraicTypeTheory.GraphTerm: Sort, Var, App, OpDecl, SortDecl, Term, Rule, Theory, render, extend, infer

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

###############
# TYPE LEVELS #
###############
Size = Sort(:lvl)
sizedecl = SortDecl(:lvl, "Hierarchy of type universes")
Zero = App(:zero)
zerodecl = OpDecl(:zero, "0", Size, "Type level of sets")
α, β, α′ = [Var(x, Size) for x in [:α,:β,:α′]]

sucdecl = OpDecl(:suc, "{}+1", Size, [α], "Successor")
αβ, αα′, α′β, = [Sort(:lt, x) for x in [[α,β],[α,α′],[α′,β]]]
orddecl = SortDecl(:lt, "{}<{}", [α,β], "A witness to the relative ordering of two universes in the type hierarchy")
p, p′, q, r = [Var(x, y) for (x, y) in zip([:p,:p′,:q,:r], [αβ,αβ,αα′,α′β])]


ltzdecl = OpDecl(:ltz, "0 < {}+1", Sort(:lt, [Zero,App(:suc, [α])]), [α], "Every rank's successor is greater than 0")
ltsdecl = OpDecl(:lts, "{1} < {1}+1", Sort(:lt, [α,App(:suc, [α])]), [α], "Every rank's successor is greater than itself")

ltldecl = OpDecl(:ltlift, "({})+1", Sort(:lt, [App(:suc, [α]),App(:suc, [β])]), [p], "Successor relation preserves ordering")

ordunidecl = Rule("Ord unique", "The sort α<β is a singleton", p, p′)
sizetrandec = OpDecl(:⪡, "binary", αβ, [q,r], "< transitivity")

cwf = extend(cwf, [sizedecl,orddecl], [sucdecl,zerodecl,ltzdecl, ltsdecl,
             ltldecl,sizetrandec], [ordunidecl], "cwf3")

######################
# TYPES AND ELEMENTS #
######################
Tydecl = SortDecl(:Ty, "Ty{}({})", [α,Γ], "The sort of types in context Γ (of size α)")
TyΓα, TyΔα = [Sort(:Ty, [α,Γ]), Sort(:Ty, [α,Δ])]
TyΓβ = Sort(:Ty, [β,Γ])
AyΓα = Var(:A, TyΓα)
elΓA = Sort(:el, [Γ,AyΓα])
Eldecl = SortDecl(:el, "𝐄𝐥({}⊢{})", [Γ, AyΓα], "The sort of terms of type A (in ctx Γ), where A is of size α
 'This is to fix a dependent presheaf El: Psh(ctx)/Tyα, i.e. a nat. trans. π: El→Tyα'")

Tyactdecl = OpDecl(:Tyact, "{}[{}]",TyΔα,[AyΓα, γ],
        "Substitution action: apply the substitution γ (of type Δ→Γ) to a some type A (in ctx Γ) to obtain a term of type Δ")


tyfunc1decl = Rule("Ty identity", "Applying the identity substitution (on ctx Γ) to a type in ctx Γ yields the same type", AyΓα, App(:Tyact, [AyΓα,idΓ]))

δγ = App(:cmp, [δ,γ])
t2t1 = App(:Tyact, [AyΓα,δγ])
AyΓαγ = App(:Tyact, [AyΓα,γ])
t2t2 = App(:Tyact, [AyΓαγ,δ])

tyfunc2decl = Rule("Ty preserves composition", """The functor to Fam from C preserves composition of substitutions:
applying two substitutions in sequence is the same as applying the composition of the substitutions in C""",
t2t1,t2t2)


a = Var(:a, elΓA)
ElΔAγ = Sort(:el, [Δ,AyΓαγ])

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
ΓA = App(:ext, [Γ,AyΓα])
ctxcmpdecl = OpDecl(:ext, "({}.{})", Ctx,[Γ,AyΓα],
                    "Context compreshension operation")
N = Var(:N, ElΔAγ)
snocdecl = OpDecl(:snoc, "⟨{},{}⟩", Sort(:Hom, [Δ,ΓA]), [γ,N], "???")
Pdecl = OpDecl(:p, "𝐩({})", Sort(:Hom, [ΓA,Γ]), [AyΓα], "Projection function 'drop'???")
P = App(:p, [AyΓα])
TyAp = App(:Tyact, [AyΓα,P])
Qdecl = OpDecl(:q, "𝐪({})", Sort(:el, [ΓA,TyAp]), [AyΓα], "Projection function 'var'???")
Q = App(:q, [AyΓα])
peq = Rule("Universal property of 𝐩", γ, App(:cmp, [App(:snoc, [γ,N]),P]))
qeq = Rule("Universal property of 𝐪", N, App(:Elact, [Q,App(:snoc, [γ,N])]))
pqeq = Rule("𝐩𝐪 property", App(:id, [ΓA]), App(:snoc, [P,Q]))
cct1 = App(:cmp, [δ,App(:snoc, [γ,N])])
cct2 = App(:snoc, [App(:cmp, [δ,γ]), App(:Elact, [N,δ])])
compcomp = Rule("Comp comp", cct1, cct2)

cwf = extend(cwf, [], [ctxcmpdecl,snocdecl,Pdecl,Qdecl], [peq,qeq,pqeq,compcomp], "cwf5")

#######################################
# Algebraic cumulativity and lifting #
#######################################
liftdecl = OpDecl(:lift,"⇧({},{})", TyΓβ, [p,AyΓα],"Lifts a type of level α to some β>α")
Lift = App(:lift, [p, AyΓα])
liftsubdecl = Rule("Lift substitution",
                    App(:lift,[p,AyΓαγ]), App(:Tyact, [Lift, γ]))
liftcmpdecl = Rule("Lift composition", Lift, App(:lift,[r, App(:lift,[q,AyΓα])]))


lifteldecl = Rule("Element lifting",elΓA ,Sort(:el, [Γ,Lift]))
liftctxdecl = Rule("Context lifting", ΓA, App(:ext,[Γ,Lift]))
cwf = extend(cwf, [], [liftdecl], [liftsubdecl, liftcmpdecl,
             lifteldecl, liftctxdecl], "cwf6")

##############################
# Type theoretic connectives #
##############################
B = Var(:B, Sort(:Ty, [α,ΓA]))
pidecl = OpDecl(:Pi, "Π({},{})", TyΓα, [AyΓα,B], "Π formation")

ΠAB = App(:Pi, [AyΓα,B])
lamsort = Sort(:el, [Γ,ΠAB])
M = Var(:M, Sort(:el, [ΓA,B]))
lamM = App(:lam,[M])
lamdecl = OpDecl(:lam, "λ({})", lamsort, [M], "Π introduction")

liftB= App(:lift,[p,B])
pild2 = App(:Pi, [Lift,liftB])
piliftdecl = Rule("Π lifting", App(:lift,[p,ΠAB]), pild2)

pisub22 = App(:Tyact,[B,App(:snoc,[App(:cmp,[P,γ]),Q])])
pisub2 = App(:Pi,[AyΓαγ, pisub22])
pisubdecl = Rule("Pi substitution", App(:Tyact,[ΠAB,γ]), pisub2)


cwf = extend(cwf, [], [pidecl, lamdecl], [pisubdecl,piliftdecl], "cwf7")
# print(render(cwf))


ΓliftA = App(:ext,[Γ,Lift])
nsort = Var(:N,Sort(:el,[ΓliftA,liftB]))
liftM = App(:lam,[Var(:N,Sort(:el,[ΓliftA,liftB]))])

# INFER is constructing an ill-formed term with liftM
# The lift operator is pointed to by node 6 and node 36
# NEED TO RESOLVE

llndecl = Rule("Lambda Lifting Naturality",lamM,liftM)

# lamsubdecl = Rule("Lambda Substitution",,)
# pieldecl = Rule("Pi Elination",,)
# appldecl = Rule("App lifting naturality",,)
# appsdecl = Rule("App substitution",,)
# piudecl = Rule("Pi Unicity",,)
# picdecl = Rule("Pi computation",,)

end

"""
################################
# ******* Theory: cwf7 ******* #
################################

6 sorts, 19 ops, 18 rules

#########
# Sorts #
#########

==================================================

---------   lvl
lvl  sort

Hierarchy of type universes


==================================================
 α,β:lvl
---------   lt
α<β  sort

A witness to the relative ordering of two universes in the type hierarchy


==================================================

---------   Ctx
Ctx  sort

Contexts: Concretely, a mapping xᵢ:Xᵢ of free variables to types.
Consider these as objects in a category C.


==================================================
Γ:Ctx  α:lvl
------------   Ty
Tyα(Γ)  sort

The sort of types in context Γ (of size α)


==================================================
 A,B:Ctx
---------   Hom
A→B  sort

Substitutions between contexts: concretely, a substitution bᵢ:βᵢ↦aᵢ:αᵢ.
Consider these as morphisms in the category C.


==================================================
A:Tyα(Γ)  Γ:Ctx  α:lvl
----------------------   el
    𝐄𝐥(Γ⊢A)  sort

The sort of terms of type A (in ctx Γ), where A is of size α
 'This is to fix a dependent presheaf El: Psh(ctx)/Tyα, i.e. a nat. trans. π: El→Tyα'


##############
# Operations #
##############

==================================================
r:α′<β  q:α<α′  α,α′,β:lvl
--------------------------   ⪡
      (q ⪡ r) : α<β

< transitivity


==================================================
  α:lvl
---------   suc
α+1 : lvl

Successor


==================================================
α,β:lvl  p:α<β
---------------   ltlift
(p)+1 : α+1<β+1

Successor relation preserves ordering


==================================================

-------   zero
0 : lvl

Type level of sets


==================================================
A:Tyα(Γ)  Γ:Ctx  α,β:lvl  p:α<β
-------------------------------   lift
        ⇧(p,A) : Tyβ(Γ)

Lifts a type of level α to some β>α


==================================================
A:Tyα(Γ)  Γ:Ctx  α:lvl
----------------------   ext
     (Γ.A) : Ctx

Context compreshension operation


==================================================
B:Tyα((Γ.A))  A:Tyα(Γ)  Γ:Ctx  α:lvl
------------------------------------   Pi
          Π(A,B) : Tyα(Γ)

Π formation


==================================================
   A:Ctx
-----------   id
id(A) : A→A

The identity morphism


==================================================
f:A→B  g:B→C  A,B,C:Ctx
-----------------------   ⋅
     (f ⋅ g) : A→C

Composition, only defined for pairs of morphisms that match head-to-tail, is an associative operation which picks out a third.


==================================================
γ:Δ→Γ  A:Tyα(Γ)  α:lvl  Γ,Δ:Ctx
-------------------------------   Tyact
         A[γ] : Tyα(Δ)

Substitution action: apply the substitution γ (of type Δ→Γ) to a some type A (in ctx Γ) to obtain a term of type Δ


==================================================

-------   emp
⋅ : Ctx

The category C has a terminal object: the empty context


==================================================
γ:Δ→Γ  A:Tyα(Γ)  α:lvl  Γ,Δ:Ctx  a:𝐄𝐥(Γ⊢A)
------------------------------------------   Elact
            a[γ] : 𝐄𝐥(Δ⊢A[γ])

Substitution action: apply the substitution γ (of type Δ→Γ) to a term of type A (in ctx Γ)
Result: a term of type A[γ] (in ctx Δ)


==================================================
B:Tyα((Γ.A))  A:Tyα(Γ)  M:𝐄𝐥((Γ.A)⊢B)  Γ:Ctx  α:lvl
---------------------------------------------------   lam
                λ(M) : 𝐄𝐥(Γ⊢Π(A,B))

Π introduction


==================================================
γ:Δ→Γ  A:Tyα(Γ)  N:𝐄𝐥(Δ⊢A[γ])  α:lvl  Γ,Δ:Ctx
---------------------------------------------   snoc
               ⟨γ,N⟩ : Δ→(Γ.A)

???


==================================================
    Γ:Ctx
--------------   empsubst
!(Γ) : Γ→emp()

Substitution into an empty context


==================================================
A:Tyα(Γ)  Γ:Ctx  α:lvl
----------------------   p
    𝐩(A) : (Γ.A)→Γ

Projection function 'drop'???


==================================================
 A:Tyα(Γ)  Γ:Ctx  α:lvl
------------------------   q
𝐪(A) : 𝐄𝐥((Γ.A)⊢A[𝐩(A)])

Projection function 'var'???


==================================================
     α:lvl
---------------   lts
α < α+1 : α<α+1

Every rank's successor is greater than itself


==================================================
       α:lvl
--------------------   ltz
0 < α+1 : zero()<α+1

Every rank's successor is greater than 0


###################
# Equality Axioms #
###################

==================================================
  η:Γ→emp()  Γ:Ctx
--------------------   ! unique
!(Γ) = η   : Γ→emp()

Substitution into an empty context is unique.


==================================================
γ:Δ→Γ  A:Tyα(Γ)  N:𝐄𝐥(Δ⊢A[γ])  α:lvl  δ:Ξ→Δ  Γ,Δ,Ξ:Ctx
------------------------------------------------------   Comp comp
       (δ ⋅ ⟨γ,N⟩) = ⟨(δ ⋅ γ),N[δ]⟩   : Ξ→(Γ.A)


==================================================
A:Tyα(Γ)  Γ:Ctx  α,β:lvl  p:α<β
-------------------------------   Context lifting
  (Γ.A) = (Γ.⇧(p,A))   : Ctx


==================================================
A:Tyα(Γ)  Γ:Ctx  α,β:lvl  p:α<β
-------------------------------   Element lifting
 𝐄𝐥(Γ⊢A) = 𝐄𝐥(Γ⊢⇧(p,A))   sort


==================================================
A:Tyα(Γ)  Γ:Ctx  r:α′<β  q:α<α′  α,α′,β:lvl  p:α<β
--------------------------------------------------   Lift composition
         ⇧(p,A) = ⇧(r,⇧(q,A))   : Tyβ(Γ)


==================================================
γ:Δ→Γ  A:Tyα(Γ)  Γ,Δ:Ctx  α,β:lvl  p:α<β
----------------------------------------   Lift substitution
    ⇧(p,A[γ]) = ⇧(p,A)[γ]   : Tyβ(Δ)


==================================================
p,p′:α<β  α,β:lvl
-----------------   Ord unique
 p = p′   : α<β

The sort α<β is a singleton


==================================================
   B:Tyα((Γ.A))  γ:Δ→Γ  A:Tyα(Γ)  α:lvl  Γ,Δ:Ctx
---------------------------------------------------   Pi substitution
Π(A,B)[γ] = Π(A[γ],B[⟨(𝐩(A) ⋅ γ),𝐪(A)⟩])   : Tyα(Δ)


==================================================
γ:Δ→Γ  A:Tyα(Γ)  α:lvl  a:𝐄𝐥(Γ⊢A)  δ:Ξ→Δ  Γ,Δ,Ξ:Ctx
---------------------------------------------------   Term substitution composition
     a[(δ ⋅ γ)] = a[γ][δ]   : 𝐄𝐥(Ξ⊢A[(δ ⋅ γ)])

The functor to Fam from C preserves composition of substitutions:
Applying two substitutions in sequence is the same as applying the composition of the substitutions in C


==================================================
A:Tyα(Γ)  Γ:Ctx  α:lvl  a:𝐄𝐥(Γ⊢A)
---------------------------------   Term substitution identity
    a = a[id(Γ)]   : 𝐄𝐥(Γ⊢A)

The identity substitution on a term yields the same term


==================================================
A:Tyα(Γ)  Γ:Ctx  α:lvl
-----------------------   Ty identity
A = A[id(Γ)]   : Tyα(Γ)

Applying the identity substitution (on ctx Γ) to a type in ctx Γ yields the same type


==================================================
γ:Δ→Γ  A:Tyα(Γ)  α:lvl  δ:Ξ→Δ  Γ,Δ,Ξ:Ctx
----------------------------------------   Ty preserves composition
    A[(δ ⋅ γ)] = A[γ][δ]   : Tyα(Ξ)

The functor to Fam from C preserves composition of substitutions:
applying two substitutions in sequence is the same as applying the composition of the substitutions in C


==================================================
γ:Δ→Γ  A:Tyα(Γ)  N:𝐄𝐥(Δ⊢A[γ])  α:lvl  Γ,Δ:Ctx
---------------------------------------------   Universal property of 𝐩
         γ = (⟨γ,N⟩ ⋅ 𝐩(A))   : Δ→Γ


==================================================
γ:Δ→Γ  A:Tyα(Γ)  N:𝐄𝐥(Δ⊢A[γ])  α:lvl  Γ,Δ:Ctx
---------------------------------------------   Universal property of 𝐪
       N = 𝐪(A)[⟨γ,N⟩]   : 𝐄𝐥(Δ⊢A[γ])


==================================================
  f:A→B  g:B→C  A,B,C,D:Ctx  h:C→D
-------------------------------------   ⋅ associativity
((f ⋅ g) ⋅ h) = (f ⋅ (g ⋅ h))   : A→D


==================================================
    f:A→B  A,B:Ctx
-----------------------   ⋅ left-identity
f = (id(A) ⋅ f)   : A→B


==================================================
    f:A→B  A,B:Ctx
-----------------------   ⋅ right-identity
f = (f ⋅ id(B))   : A→B


==================================================
        A:Tyα(Γ)  Γ:Ctx  α:lvl
---------------------------------------   𝐩𝐪 property
id((Γ.A)) = ⟨𝐩(A),𝐪(A)⟩   : (Γ.A)→(Γ.A)
"""