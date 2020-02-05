# AlgebraicTypeTheory.jl
Based on [this tutorial](http://www.jonmsterling.com/pdfs/algebraic-type-theory-tutorial.pdf) and [this paper](https://arxiv.org/abs/1902.08848) by Jonathan Sterling. This is just experimentation with ideas that might be useful for Catlab.jl.

## Goals
The first purpose is to construct *theories*, which are collections of sort declarations, (term) operation declarations, and equality axioms (between sorts and/or terms).

The second purpose is to *instantiate* theories using Julia types and functions.

The next goal would be represent homomorphisms between theories and to be able to compose these to get new instances from old ones. Another would be to look at the structure of some theories and automatically infer some natural morphisms (e.g. an injection from a smaller theory).

## Status

Implementations for boolean algebras, preorders, monoids, categories, and partially through the algebraicized Martin-Löf type theory that makes up the bulk of the tutorial linked above.

The roadblock for this last implementation is the need for determining when two sorts are equivalent (only when there are no sort equality axioms, this is trivial).
