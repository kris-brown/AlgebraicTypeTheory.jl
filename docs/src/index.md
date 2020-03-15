# AlgebraicTypeTheory.jl
So far, based on [this tutorial](http://www.jonmsterling.com/pdfs/algebraic-type-theory-tutorial.pdf) and [this paper](https://arxiv.org/abs/1902.08848) by Jonathan Sterling.

## Goals

- [x] To experiment with ideas that might be useful for [Catlab.jl](https://epatters.github.io/Catlab.jl/latest/).

- [x] To construct *theories*, which are collections of sort declarations, (term) operation declarations, and equality axioms (between sorts and/or terms).

- [x] To *instantiate* theories using Julia types and functions, so that terms of the theory can be concretely evaluated.

- [ ] To use a theory to rewrite terms of that theory in a normal form.

- [ ] To represent homomorphisms between theories and to be able to compose these to get new instances from old ones.

- [ ] To look at the structure of some theories and automatically infer some natural morphisms (e.g. an injection from a strictly smaller theory).

- [ ] To organize a collection of theories into a queryable knowledge base.

- [ ]To use macros to make the writing of equations/theories more convenient. E.g.
```
   App(:mul, [
      App(:mul, [
         App(:mul, [
               App(:mul, [
                  App(:mul,[
                     App(:id),
                     X]),
                  Y]),
               Z]),
         App(:id)]),
      X])
```
could be written as `@term (((((id() * X) * Y) * Z) * id()) * X)`

## Status

Theories: implementations for Boolean algebras, preorders, monoids, categories, an algebraicized Martin-Löf type theory (not complete yet).

Current roadblock: in order to apply rewrite rules to an expression, we need to be able to infer its sort and the sorts of its subterms. This is done by simple pattern matching of expressions: an declaring an operation involves declaring a result sort pattern and term patterns for each argument - by matching terms, we can plug in to the sort pattern and get the result (also effectively typechecking all terms). However, the structure of a term is itself modulo the rewrite rules of the theory, so if there are rewrite rules on sorts or rewrite rules that change the structure of the sort of a term, then things that should be valid arguments will fail to pattern match. As of yet the only theory considered that cannot be fully formalized is the Dependent Types / Categories with Families example.

To address this, a rewriting algorithm needs to be implemented. Currently, we can rewrite a term by applying a particular rewrite rule at a particular point in the term graph, but what's needed is an algorithm which searches of the rules of a theory and repeatedly applies rewrite rules to get to a normal form (ideally the rewrite system is terminating and confluent).

## Overview

### Terms, Patterns, Rewrite rules
Take the theory of categories and create a term: `Var(:f,Sort(:Hom,[Var(:A,Ob),Var(:A,Ob)]))` (using `Ob=Sort(:Ob)`)


```@raw html
<style>
.iframe li {
  width: 100% !important;
  height: 525 !important;
}
</style>

<iframe id="igraph" style="border:none;" seamless="seamless" src="https://web.stanford.edu/~ksb/docs/f.html" height="525" width="100%"></iframe>
```

We can define composition by providing the output sort, `Sort(:Hom,[Var(:X,Ob),Var(:Z,Ob)])`. Here the variables actually are meant to be wildcards, so we can create a new symbol in our graph to mean "something (arg #2) of a certain sort (arg #1)" and let the "something" be matchable with anything.

```@raw html
<iframe id="igraph" style="border:none;" seamless="seamless" src="https://web.stanford.edu/~ksb/docs/homxzpat.html" height="525" width="100%"></iframe>
```

The variable names were significant (note each wildcard has a name) since these names can be bound in the arguments of the declaration of composition, which are `Var(:m,Sort(:Hom,[Var(:X,Ob),Var(:Y,Ob)])])` and `Var(:n,Sort(:Hom,[Var(:Y,Ob),Var(:Z,Ob)])])` (the variable names `m` and `n` only matter for printing out the operator declaration, and all that was important for `Y` was that it was the same the two arguments). Now we can compute the sort of arbitrary expressions that match this pattern. So using a theory we can "upgrade" a term like `App(:cmp,[App(:id,[Var(:A,Ob)]), Var(:f,Sort(:Hom,[Var(:A,Ob),Var(:B,Ob)]))])`:

```@raw html
<iframe id="igraph" style="border:none;" seamless="seamless" src="https://web.stanford.edu/~ksb/docs/idf.html" height="525" width="100%"></iframe>
```
...to a "sorted version":

```@raw html
<iframe id="igraph" style="border:none;" seamless="seamless" src="https://web.stanford.edu/~ksb/docs/idfinferred.html" height="525" width="100%"></iframe>
```
We can then create pattern out of this and `f` by itself to make a rule: `Rule("⋅ left-identity", f, App(:cmp, [idA,f]))` which can perform the left rewrite identity on any graph term of an identity composed with something.

### Example theory

Sort declarations, term operation declarations, and axioms all can be rendered in plain text, and sorts/terms/patterns may as viewed as term graphs. For example, this fragment of categories with families + dependent types.

```

################################
# ******* Theory: cwf ******* #
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
```

### Computing with GATs

We can define an instance of a theory by mapping (possibly parameterized) types to sorts and functions to the term operations.

