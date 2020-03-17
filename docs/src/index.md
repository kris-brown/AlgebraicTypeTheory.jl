# AlgebraicTypeTheory.jl
So far, encoding material from [this tutorial](http://www.jonmsterling.com/pdfs/algebraic-type-theory-tutorial.pdf) and [this paper](https://arxiv.org/abs/1902.08848) by Jonathan Sterling.

## Goals

- [x] To experiment with ideas that might be useful for [Catlab.jl](https://epatters.github.io/Catlab.jl/latest/).

- [x] To construct *theories*, which are collections of sort declarations, (term) operation declarations, and equality axioms (between sorts and/or terms).

- [x] To *instantiate* theories using Julia types and functions, so that terms of the theory can be concretely evaluated.

- [ \ ] To use a theory to rewrite terms of that theory in a normal form.

- [  ] Test (by exhaustive or random search) that instances of theories satisfy their axioms

- [  ] To represent homomorphisms between theories and to be able to compose these to get new instances from old ones.

- [  ] To look at the structure of some theories and automatically infer some natural morphisms (e.g. an injection from a strictly smaller theory).

- [  ] To organize a collection of theories into a queryable knowledge base.

- [  ]To use macros to make the writing of equations/theories more convenient. E.g.
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

Theories: implementations for [Boolean algebras](https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/src/theories/Boolean.jl), [preorders](https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/src/theories/Preorder.jl), [monoids](https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/src/theories/Monoid.jl), [categories](https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/src/theories/Cat.jl), an [algebraicized Martin-Löf type theory](https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/src/theories/Cwf_no_level.jl) (not complete yet).

## Overview

### Terms, Patterns, Rewrite rules
Take the theory of categories and create a term: `Var(:f,Sort(:Hom,[Var(:A,Ob),Var(:A,Ob)]))` (using `Ob=Sort(:Ob)`)


```@raw html
<iframe style="height: 625px;" id="igraph" style="border:none;" seamless="seamless" src="https://web.stanford.edu/~ksb/docs/f.html" height="525" width="100%"></iframe>
```

We can define composition by providing the output sort, `Sort(:Hom,[Var(:X,Ob),Var(:Z,Ob)])`. Here the variables actually are meant to be wildcards, so we can create a new symbol in our graph to mean "something (arg #2) of a certain sort (arg #1)" and let the "something" be matchable with anything.

```@raw html
<iframe style="height: 625px;" id="igraph" style="border:none;" seamless="seamless" src="https://web.stanford.edu/~ksb/docs/homxzpat.html" height="525" width="100%"></iframe>
```

The variable names were significant (note each wildcard has a name) since these names can be bound in the arguments of the declaration of composition, which are `Var(:m,Sort(:Hom,[Var(:X,Ob),Var(:Y,Ob)])])` and `Var(:n,Sort(:Hom,[Var(:Y,Ob),Var(:Z,Ob)])])` (the variable names `m` and `n` only matter for printing out the operator declaration, and all that was important for `Y` was that it was the same in the two arguments). Now we can compute the sort of arbitrary expressions that match this pattern. So using a theory we can "upgrade" a term like `App(:cmp,[App(:id,[Var(:A,Ob)]), Var(:f,Sort(:Hom,[Var(:A,Ob),Var(:B,Ob)]))])`:

```@raw html
<iframe scrolling="no" style="height: 625px;" id="igraph" style="border:none;" seamless="seamless" src="https://web.stanford.edu/~ksb/docs/idf.html" height="525" width="100%"></iframe>
```
...to a "sorted version":

```@raw html
<iframe scrolling="no" style="height: 625px;" id="igraph" style="border:none;" seamless="seamless" src="https://web.stanford.edu/~ksb/docs/idfinferred.html" height="525" width="100%"></iframe>
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
γ:Δ→Γ  A:Ty(Γ)  N:𝐄𝐥(Δ⊢A[γ])  Γ,Δ:Ctx
-------------------------------------   Universal property of 𝐩
      γ = (⟨γ,N⟩⋅𝐩(A))   : Δ→Γ

==================================================
γ:Δ→Γ  A:Ty(Γ)  N:𝐄𝐥(Δ⊢A[γ])  Γ,Δ:Ctx
-------------------------------------   Universal property of 𝐪
   N = 𝐪(A)[⟨γ,N⟩]   : 𝐄𝐥(Δ⊢A[γ])
==================================================
            A:Ty(Γ)  Γ:Ctx
---------------------------------------   𝐩𝐪 property
id((Γ.A)) = ⟨𝐩(A),𝐪(A)⟩   : (Γ.A)→(Γ.A)
```
### Normalization rules
A naive normalization algorithm is implemented to simplify terms, hopefully to a normal form (if the axioms, interpreted as rewrite rules, are confluent and terminating). It tries to apply all rules to all nodes in the tree, restarting when a change is made. If a cycle is detected, then the process stops and returns the lexicographic maximum (to resolve `(X+Y)<->(Y+X)` infinite loops and others). Examples, including `((id(A) ⋅ ((ab ⋅ bc) ⋅ id(C))) ⋅ (id(C) ⋅ (id(C) ⋅ cd))) -> ((ab ⋅ bc) ⋅ cd)`, are in a [test file](https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/test/testnorm.jl).

### Computing with GATs

We can define an instance of a theory by mapping (possibly parameterized) types to sorts and functions to the term operations. In a [test file](https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/test/testinst.jl) there are examples of implementing Monoids with `(Int,*)`, Boolean algebras with the powerset of `{1,2,3}` and union/intersection/complement, and Categories with 2D matrix multiplication. For instance, the following term can be evaluated in an environment where `f=[1, 2, 3; 4, 5, 6], g=[1;1;1], M=ℤ², N=ℤ³, P=ℤ`

```@raw html
<iframe scrolling="no" style="height: 625px;" id="igraph" style="border:none;" seamless="seamless" src="https://web.stanford.edu/~ksb/docs/idfg.html" height="525" width="100%"></iframe>
```

to obtain the composite `[6; 15]` which transforms from ℤ² to ℤ. We can reduce the number of computations by reducing the expression using `Cat`'s rewrite rules before evaluating.

