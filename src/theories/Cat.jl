module Cat
export cat, cat_inferred

if isdefined(@__MODULE__, :LanguageServer)
    include("../AlgebraicTypeTheory.jl")
    include("../GraphTerm.jl")
    include("../CVC.jl")
    using .GraphTerm
else
    using AlgebraicTypeTheory.GraphTerm: Sort, Var, App, OpDecl, SortDecl, Term, Rule, Theory, render, uninfer, infer, patmatch, sub, viz
    using AlgebraicTypeTheory.CVC: writeFile
end

Ob = Sort(:Ob)
Obdecl = SortDecl(:Ob, "Object of category")
α, β, θ, A, B, C, D = [Var(x, Ob) for x in [:α,:β,:θ,:A,:B,:C,:D]]
Hom_aa, Hom_ab, Hom_bc, Hom_cd, Hom_αα, Hom_αβ, Hom_αθ, Hom_βθ = [Sort(:Hom, x) for x in [ [A,A],[A,B],[B,C],[C,D],[α,α],[α,β],[α,θ],[β,θ]]]
f, g, h, γ, δ = [Var(x, h) for (x, h) in zip([:f,:g,:h,:γ,:δ], [Hom_ab,Hom_bc,Hom_cd,Hom_αβ,Hom_βθ])]

Homdecl = SortDecl(:Hom, 2, [α, β], "Hom-set of morphisms from α to β")
iddecl = OpDecl(:id, 1, Hom_αα, [α], "The identity morphism")

cmpdecl = OpDecl(:cmp, "({} ⋅ {})", Hom_αθ, [γ,δ], "Composition, only defined for pairs of morphisms that match head-to-tail, is an associative operation which picks out a third.")

idA, idB = [App(:id, [x]) for x in [A,B]]
fg, gh = [App(:cmp, x) for x in [[f,g],[g,h]]]

f_gh, fg_h = [App(:cmp, x) for x in [[fg,h],[f,gh]]]

idAf =  App(:cmp, [idA,f])
idldecl = Rule("⋅ left-identity", f,idAf)
idrdecl = Rule("⋅ right-identity", f, App(:cmp, [f,idB]))
ascdecl = Rule("⋅ associativity", f_gh, fg_h)

cat = Theory([Obdecl,Homdecl], [iddecl,cmpdecl], [idldecl,idrdecl,ascdecl], "Category", true)

cat_inferred = Theory([Obdecl,Homdecl], [iddecl,cmpdecl], [idldecl,idrdecl,ascdecl], "Category")

default_examples = Dict("idAf" => idAf, "f" => f)

function writeCVC(depth::Int=3, examples::Dict{String,Term}=default_examples)::Nothing
    @assert haskey(ENV, "CVC4ROOT")
    writeFile(cat_inferred, examples, ENV["CVC4ROOT"] * "/Category.cvc", depth)
    return nothing
end

end
"""
####################################
# ******* Theory: Category ******* #
####################################

2 sorts, 2 ops, 3 rules

#########
# Sorts #
#########

==================================================

--------   Ob
Ob  sort

Object of category


==================================================
    α,β:Ob
--------------   Hom
Hom(α,β)  sort

Hom-set of morphisms from α to β


##############
# Operations #
##############

==================================================
      α:Ob
----------------   id
id(α) : Hom(α,α)

The identity morphism


==================================================
γ:Hom(α,β)  α,β,θ:Ob  δ:Hom(β,θ)
--------------------------------   ⋅
       (γ ⋅ δ) : Hom(α,θ)

Composition, only defined for pairs of morphisms that match head-to-tail, is an associative operation which picks out a third.


###################
# Equality Axioms #
###################

==================================================
f:Hom(A,B)  g:Hom(B,C)  A,B,C,D:Ob  h:Hom(C,D)
----------------------------------------------   ⋅ associativity
   ((f ⋅ g) ⋅ h) = (f ⋅ (g ⋅ h)) : Hom(A,D)


==================================================
    f:Hom(A,B)  A,B:Ob
--------------------------   ⋅ left-identity
f = (id(A) ⋅ f) : Hom(A,B)


==================================================
    f:Hom(A,B)  A,B:Ob
--------------------------   ⋅ right-identity
f = (f ⋅ id(B)) : Hom(A,B)
"""
