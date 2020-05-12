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

Theories: implementations for [Boolean algebras](https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/src/theories/Boolean.jl), [preorders](https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/src/theories/Preorder.jl), [monoids](https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/src/theories/Monoid.jl), [categories](https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/src/theories/Cat.jl), an [algebraicized Martin-Löf type theory](https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/src/theories/Cwf.jl) (not complete yet).

## Overview

### Terms, Patterns, Rewrite rules
Take the theory of categories and let `Ob=Sort(:Ob); A,B,C,X,Y,Z = [Var(x, Ob) for x in [:A,:B,:C,:X,:Y,:Z]]` so that we can create a term: `Var(:f, Sort(:Hom,[A,B]))`


```@raw html
<iframe scrolling="no" style="height: 625px;" id="igraph" style="border:none;" seamless="seamless" src="https://web.stanford.edu/~ksb/docs/f.html" height="525" width="100%"></iframe>
```

We can define composition by providing the output sort and then the sorts of arguments: `OpDecl(:cmp, Sort(:Hom,[X,Z]), [Sort(:Hom,[X,Y])]),Sort(:Hom,[Y,Z])])` Here the variables actually signify wildcards, so these terms gets automatically turned into patterns with named wildcards and a new dark cross symbol which means "I have a term (arg #2) of a certain sort (arg #1)". This is what the output sort looks like:

```@raw html
<iframe scrolling="no" style="height: 625px;" id="igraph" style="border:none;" seamless="seamless" src="https://web.stanford.edu/~ksb/docs/homxzpat.html" height="525" width="100%"></iframe>
```
Now we can compute the sort of arbitrary expressions that match this pattern. So using a theory we can "upgrade" a term like `App(:cmp,[App(:id,[A]), Var(:f,Sort(:Hom,[A,B]))])`:

```@raw html
<iframe scrolling="no" style="height: 625px;" id="igraph" style="border:none;" seamless="seamless" src="https://web.stanford.edu/~ksb/docs/idf.html" height="525" width="100%"></iframe>
```
...to a "sorted version":

```@raw html
<iframe scrolling="no" style="height: 625px;" id="igraph" style="border:none;" seamless="seamless" src="https://web.stanford.edu/~ksb/docs/idfinferred.html" height="525" width="100%"></iframe>
```
We can then create pattern out of this and `f` by itself to make a rule: `Rule("⋅ left-identity", f, App(:cmp, [idA,f]))` which can perform the left rewrite identity on any graph term of an identity composed with something.

### Normalization rules
A naive normalization algorithm is implemented to simplify terms, hopefully to a normal form (if the axioms, interpreted as rewrite rules, are confluent and terminating). It tries to apply all rules to all nodes in the tree, restarting when a change is made. If a cycle is detected, then the process stops and returns the lexicographic maximum (to resolve `(X+Y)<->(Y+X)` infinite loops and others). Examples, including `((id(A) ⋅ ((ab ⋅ bc) ⋅ id(C))) ⋅ (id(C) ⋅ (id(C) ⋅ cd))) -> ((ab ⋅ bc) ⋅ cd)`, are in a [test file](https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/test/testnorm.jl).

### Computing with GATs

We can define an instance of a theory by mapping (possibly parameterized) types to sorts and functions to the term operations. In a [test file](https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/test/testinst.jl) there are examples of implementing Monoids with `(Int,*)`, Boolean algebras with the powerset of `{1,2,3}` and union/intersection/complement, and Categories with 2D matrix multiplication. For instance, the following term can be evaluated in an environment where `f=[1, 2, 3; 4, 5, 6], g=[1;1;1], M=ℤ², N=ℤ³, P=ℤ`

```@raw html
<iframe scrolling="no" style="height: 625px;" id="igraph" style="border:none;" seamless="seamless" src="https://web.stanford.edu/~ksb/docs/idfg.html" height="525" width="100%"></iframe>
```

to obtain the composite `[6; 15]` which transforms from ℤ² to ℤ. We can reduce the number of computations by reducing the expression using `Cat`'s rewrite rules before evaluating.

