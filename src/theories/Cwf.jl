module Cwf
export cwf
if isdefined(@__MODULE__, :LanguageServer)
    include("../GraphTerm.jl")
    using .GraphTerm
else
    using AlgebraicTypeTheory.GraphTerm: Sort, Var, App, OpDecl, SortDecl, Term, Rule, Theory, render, uninfer, infer, patmatch, sub
end

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




ΓliftA = App(:ext,[Γ,Lift])
nsort = Var(:N,Sort(:el,[ΓliftA,liftB]))
liftM = App(:lam,[nsort])
llndecl = Rule("Lambda Lifting Naturality",lamM,liftM)

lamMy = App(:Tyact, [lamM, γ])
yopq = App(:snoc,[App(:cmp,[P,γ]), Q])
lamMypq = App(:lam,[App(:Elact, [M, yopq])])
lamsubdecl = Rule("Lambda Substitution", lamMy, lamMypq)

appsort = Sort(:el, [Γ, App(:Tyact, [B, App(:snoc,[idΓ, a])])])

λM = Var(:M, lamsort)
appdecl = OpDecl(:app, 2, appsort, [λM,a], "Pi elimination")
λMa  = App(:app, [λM,a])

λMalift = App(:app, [nsort,a])
appldecl = Rule("App lifting naturality", "This is confusingly notated in the paper. Cannot be checked until we have type-checking.",
                 λMa, λMalift)
as2 = App(:app,[App(:Elact,[λM,γ]), App(:Elact,[a,γ])])
appsdecl = Rule("App substitution",App(:Elact, [λMa, γ]),as2)
pu2 = App(:lam,[App(:app,[App(:Elact,[M,P]), Q])])
piudecl = Rule("Pi Unicity",λM,pu2)

picdecl = Rule("Pi computation",App(:app,[M,a]),App(:Elact,[M,App(:snoc,[idΓ,a])]))

cwf = extend(cwf, [], [pidecl, lamdecl, appdecl], [pisubdecl,piliftdecl, llndecl,
    lamsubdecl, appldecl, appsdecl, piudecl,picdecl], "cwf7", true)


print(render(cwf, picdecl))

end
