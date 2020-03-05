export cwf,compcomp

using AlgebraicTypeTheory: SortOp, Sort, TermOp, Var, OpDecl, SortDecl, App, EqDecl, mkTheory, Judgment,render, apply_rewrite, extend

############
# CONTEXTS #
############
ctx, siz, Hom = [SortOp(x,i) for (x,i) in zip([:Ctx,:size, :Hom],[0,0,"({}→{})"])]
Ctx,Size = map(Sort,[ctx,siz])
α,β,θ,A,B,C,D,Γ,Δ,Ξ = [Var(x,Ctx) for x in [:α,:β,:θ,:A,:B,:C,:D,:Γ,:Δ,:Ξ]]

Hom_aa,Hom_bb,Hom_ab,Hom_bc,Hom_ac,Hom_cd,Hom_αα,Hom_ββ,Hom_αβ,Hom_αθ,Hom_βθ,Hom_ΔΓ,HomΞΔ = [Sort(Hom, x) for x in [ [A,A],[B,B],[A,B],[B,C],[A,C],[C,D],[α,α],[β,β],[α,β],[α,θ],[β,θ],[Δ,Γ],[Ξ,Δ]]]

ctxdecl = SortDecl(Ctx,"""Contexts: Concretely, a mapping xᵢ:Xᵢ of free variables to types.
                          Consider these as objects in a category C.""")
homdecl = SortDecl(Hom_αβ, [α,β], "Substitutions between contexts: concretely, a substitution bᵢ:βᵢ↦aᵢ:αᵢ.
                                   Consider these as morphisms in the category C.")
id = TermOp(:id,1)
iddecl = OpDecl(id, Hom_αα, [α], "An identity substitution aᵢ:αᵢ↦aᵢ:αᵢ.")
f,g,h,γ,δ = [Var(x,h) for (x,h) in zip([:f,:g,:h,:γ,:δ],[Hom_ab,Hom_bc,Hom_cd,Hom_ΔΓ,HomΞΔ])]
Cmp = TermOp(:⋅,"binary")
Cmpdecl = OpDecl(Cmp,Hom_ac,[f,g], "Composition of substitutions, only defined for pairs that match contexts head-to-tail, is an associative operation which yields a third substitution.")
fg, gh = [App(Cmp,x) for x in [[f,g],[g,h]]]
idA,idB,idΓ = [App(id,[x]) for x in [A,B,Γ]]
f_gh, fg_h = [App(Cmp,x) for x in [[fg,h],[f,gh]]]

idldecl = EqDecl("⋅ left-identity", f, App(Cmp,[idA,f]))
idrdecl = EqDecl("⋅ right-identity", f, App(Cmp,[f,idB]))
ascdecl = EqDecl("⋅ associativity", f_gh, fg_h)

category = mkTheory("category", Judgment[ctxdecl, homdecl, iddecl, Cmpdecl,
                                         idldecl, idrdecl, ascdecl])

####################
# TERMINAL CONTEXT #
####################

Emp = TermOp(:emp,"⋅")
empdecl = OpDecl(Emp,Ctx,"The category C has a terminal object: the empty context")
emp = App(Emp)
Trm = TermOp(:empsubst,"!({})")
termsort = Sort(Hom,[Γ,emp])
termΓ = App(Trm,[Γ])
anyTermΓ = Var(:η,termsort)
termdecl=OpDecl(Trm,termsort,[Γ])
termundecl = EqDecl("! unique",termΓ, anyTermΓ, "The unique substitution into an empty context.")

c_t = extend(category, Judgment[empdecl, termdecl, termundecl], "c+t")

###############
# TYPE LEVELS #
###############
Size = Sort(SortOp(:lvl))
sizedecl = SortDecl(Size,"Hierarchy of type universes")
zero = TermOp(Symbol("0"))
Zero = App(zero)
zerodecl = OpDecl(zero, Size)
α, β, α′ = [Var(x,Size) for x in [:α,:β,:α′]]

suc = TermOp(:suc,"{}+1")
sucdecl = OpDecl(suc, Size, [α])
ord = SortOp(Symbol("<"),"binary")
αβ,αα′,α′β, = [Sort(ord,x) for x in [[α,β],[α,α′],[α′,β]]]
orddec = SortDecl(αβ,[α,β], "Strict ordering of type hierarchy")
p,p′,q,r = [Var(x,y) for (x,y) in zip([:p,:p′,:q,:r],[αβ,αβ,αα′,α′β])]

ltz = TermOp(:ltz, "0 < {}+1")
ltzdecl = OpDecl(ltz,Sort(ord,[Zero,App(suc,[α])]), [α])
lts = TermOp(:lts, "{1} < {1}+1")
ltsdecl = OpDecl(lts,Sort(ord,[α,App(suc,[α])]),[α])
ltlift = TermOp(:ltlift, "{}+1 < {}+1")
ltldecl = OpDecl(ltlift, Sort(ord,[App(suc,[α]),App(suc,[β])]), [α,β])

ordunidecl = EqDecl("Ord unique",p,p′,"The sort α<β is a singleton")
sizetran = TermOp(:⪡,"binary")
sizetrandec = OpDecl(sizetran,αβ,[q,r],"< transitivity")

level = mkTheory("level", Judgment[sizedecl, sucdecl, zerodecl, orddec,
                ltzdecl,ltsdecl,ltldecl,ordunidecl,sizetrandec])
c_t_l = extend(c_t, level, "c_t_l")

######################
# TYPES AND ELEMENTS #
######################
Ty = SortOp(:Ty, "Ty{}({})")
TyΓα,TyΔα = [Sort(Ty, [α,Γ]), Sort(Ty,[α,Δ])]
AyΓα, ByΔα = [Var(:A, TyΓα), Var(:B,TyΔα)]
Tydecl = SortDecl(TyΓα, [α,Γ], "The sort of types in context Γ (of size α)")

El = SortOp(:el, "𝐄𝐥({}⊢{})")
elΓA = Sort(El,[Γ,AyΓα])
Eldecl = SortDecl(elΓA, [Γ, AyΓα], "The sort of terms of type A (in ctx Γ), where A is of size α
 'This is to fix a dependent presheaf El: Psh(ctx)/Tyα, i.e. a nat. trans. π: El→Tyα'")

Tyact = TermOp(:Tyact,"{}[{}]")
Tyactdecl = OpDecl(Tyact,TyΔα,[AyΓα, γ],
        "Substitution action: apply the substitution γ (of type Δ→Γ) to a some type A (in ctx Γ) to obtain a term of type Δ")

tyfunc1decl = EqDecl("Ty identity",AyΓα,App(Tyact,[AyΓα,idΓ]),
                     "Applying the identity substitution (on ctx Γ) to a type in ctx Γ yields the same type")

δγ = App(Cmp,[δ,γ])
t2t1 = App(Tyact,[AyΓα,δγ])
t2t2_ = App(Tyact,[AyΓα,γ])
t2t2 = App(Tyact,[t2t2_,δ])

tyfunc2decl = EqDecl("Ty preserves composition", t2t1,t2t2,
     """The functor to Fam from C preserves composition of substitutions:
        applying two substitutions in sequence is the same as applying the composition of the substitutions in C""")

Elact = TermOp(:Elact,"{}[{}]")
M = Var(:M,elΓA)
ElΔAγ = Sort(El,[Δ,App(Tyact,[AyΓα,γ])])

Elactdecl = OpDecl(Elact,ElΔAγ,[M,γ],
        """Substitution action: apply the substitution γ (of type Δ→Γ) to a term of type A (in ctx Γ)
           Result: a term of type A[γ] (in ctx Δ)""")

eliddecl=EqDecl("Term substitution identity", M, App(Elact, [M,idΓ]),
                "The identity substitution on a term yields the same term")
elcompdecl = EqDecl("Term substitution composition",
                    App(Elact,[M,δγ]), App(Elact,[App(Elact,[M,γ]),δ]),
                    """The functor to Fam from C preserves composition of substitutions:
                       Applying two substitutions in sequence is the same as applying the composition of the substitutions in C""")

typel = Judgment[Tydecl,Eldecl,Tyactdecl,
           tyfunc1decl, tyfunc2decl, Elactdecl, eliddecl, elcompdecl]

ctlt = extend(c_t_l,typel, "ctlt")

#########################
# CONTEXT COMPREHENSION #
#########################
ctxcmp = TermOp(:ext,"({}.{})")
ΓA = App(ctxcmp, [Γ,AyΓα])
ctxcmpdecl = OpDecl(ctxcmp, Ctx,[Γ,AyΓα],
                    "Context compreshension operation")
snoc = TermOp(:snoc,"⟨{},{}⟩")
N = Var(:N, ElΔAγ)
snocdecl = OpDecl(snoc,Sort(Hom,[Δ,ΓA]),[γ,N], "???")
P = TermOp(:𝐩,1)
Pdecl = OpDecl(P,Sort(Hom,[ΓA,Γ]),[AyΓα],"Projection function 'drop'???")
Q = TermOp(:𝐪,1)
TyAp = App(Tyact,[AyΓα,App(P,[AyΓα])])
Qdecl = OpDecl(Q,Sort(El,[ΓA,TyAp]),[AyΓα], "Projection function 'var'???")

peq = EqDecl("Universal property of 𝐩", γ, App(Cmp,[App(snoc,[γ,N]),App(P,[AyΓα])]))
qeq = EqDecl("Universal property of 𝐪", N, App(Elact,[App(Q,[AyΓα]),App(snoc,[γ,N])]))
pqeq = EqDecl("𝐩𝐪 property", App(id,[ΓA]),App(snoc,[App(P,[AyΓα]),App(Q,[AyΓα])]))




ctx = Judgment[ctxcmpdecl,snocdecl,Pdecl,Qdecl,peq,qeq,pqeq]

cwf = extend(ctlt,ctx,"ctltc")

# WORKSHOP #
cct1 = App(Cmp,[δ,App(snoc,[γ,N])])
M = Var(:M,N.sort)
cct2 = App(snoc,[App(Cmp,[δ,γ]), App(Elact,[M,δ])])
# ct2 = infer(cwf,cct2.args[2])
# ct2n = normalize(cwf,ct2)
compcomp = EqDecl("Context comprehension composition",cct1,cct2)
