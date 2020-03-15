var documenterSearchIndex = {"docs":
[{"location":"generated/core/graphterm/#","page":"Making instances","title":"Making instances","text":"EditURL = \"https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/docs/literate/core/graphterm.jl\"","category":"page"},{"location":"generated/core/graphterm/#Making-instances-1","page":"Making instances","title":"Making instances","text":"","category":"section"},{"location":"generated/core/graphterm/#","page":"Making instances","title":"Making instances","text":"if isdefined(@__MODULE__, :LanguageServer)\n    include(\"../../../src/AlgebraicTypeTheory.jl\")\nend\nusing AlgebraicTypeTheory","category":"page"},{"location":"generated/theories/cwf_no_level/#","page":"Categories with Families (no universe levels)","title":"Categories with Families (no universe levels)","text":"EditURL = \"https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/docs/literate/theories/cwf_no_level.jl\"","category":"page"},{"location":"generated/theories/cwf_no_level/#Categories-with-Families-(no-universe-levels)-1","page":"Categories with Families (no universe levels)","title":"Categories with Families (no universe levels)","text":"","category":"section"},{"location":"generated/theories/cwf_no_level/#","page":"Categories with Families (no universe levels)","title":"Categories with Families (no universe levels)","text":"if isdefined(@__MODULE__, :LanguageServer)\n    include(\"../../../src/AlgebraicTypeTheory.jl\")\nend\n\nusing AlgebraicTypeTheory","category":"page"},{"location":"generated/theories/cwf_no_level/#","page":"Categories with Families (no universe levels)","title":"Categories with Families (no universe levels)","text":"print(render(AlgebraicTypeTheory.Theories.cwf))","category":"page"},{"location":"generated/theories/preorder/#","page":"Preorder","title":"Preorder","text":"EditURL = \"https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/docs/literate/theories/preorder.jl\"","category":"page"},{"location":"generated/theories/preorder/#Preorder-1","page":"Preorder","title":"Preorder","text":"","category":"section"},{"location":"generated/theories/preorder/#","page":"Preorder","title":"Preorder","text":"if isdefined(@__MODULE__, :LanguageServer)\n    include(\"../../../src/AlgebraicTypeTheory.jl\")\nend\n\nusing AlgebraicTypeTheory","category":"page"},{"location":"generated/theories/preorder/#","page":"Preorder","title":"Preorder","text":"print(render(AlgebraicTypeTheory.Theories.preorder))","category":"page"},{"location":"generated/theories/cwf/#","page":"Categories with Families","title":"Categories with Families","text":"EditURL = \"https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/docs/literate/theories/cwf.jl\"","category":"page"},{"location":"generated/theories/cwf/#Categories-with-Families-1","page":"Categories with Families","title":"Categories with Families","text":"","category":"section"},{"location":"generated/theories/cwf/#","page":"Categories with Families","title":"Categories with Families","text":"if isdefined(@__MODULE__, :LanguageServer)\n    include(\"../../../src/AlgebraicTypeTheory.jl\")\nend\n\nusing AlgebraicTypeTheory","category":"page"},{"location":"generated/theories/cwf/#","page":"Categories with Families","title":"Categories with Families","text":"print(render(AlgebraicTypeTheory.Theories.cwf))","category":"page"},{"location":"generated/theories/cat/#","page":"Categories","title":"Categories","text":"EditURL = \"https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/docs/literate/theories/cat.jl\"","category":"page"},{"location":"generated/theories/cat/#Categories-1","page":"Categories","title":"Categories","text":"","category":"section"},{"location":"generated/theories/cat/#","page":"Categories","title":"Categories","text":"if isdefined(@__MODULE__, :LanguageServer)\n    include(\"../../../src/AlgebraicTypeTheory.jl\")\nend\n\nusing AlgebraicTypeTheory","category":"page"},{"location":"generated/theories/cat/#","page":"Categories","title":"Categories","text":"print(render(AlgebraicTypeTheory.Theories.cat))","category":"page"},{"location":"generated/core/graph/#","page":"Core datatypes","title":"Core datatypes","text":"EditURL = \"https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/docs/literate/core/graph.jl\"","category":"page"},{"location":"generated/core/graph/#Core-datatypes-1","page":"Core datatypes","title":"Core datatypes","text":"","category":"section"},{"location":"generated/core/graph/#","page":"Core datatypes","title":"Core datatypes","text":"if isdefined(@__MODULE__, :LanguageServer)\n    include(\"../../../src/AlgebraicTypeTheory.jl\")\nend\n\nusing AlgebraicTypeTheory","category":"page"},{"location":"generated/theories/boolean/#","page":"Boolean Algebra","title":"Boolean Algebra","text":"EditURL = \"https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/docs/literate/theories/boolean.jl\"","category":"page"},{"location":"generated/theories/boolean/#Boolean-Algebra-1","page":"Boolean Algebra","title":"Boolean Algebra","text":"","category":"section"},{"location":"generated/theories/boolean/#","page":"Boolean Algebra","title":"Boolean Algebra","text":"if isdefined(@__MODULE__, :LanguageServer)\n    include(\"../../../src/AlgebraicTypeTheory.jl\")\nend\n\nusing AlgebraicTypeTheory","category":"page"},{"location":"generated/theories/boolean/#","page":"Boolean Algebra","title":"Boolean Algebra","text":"print(render(AlgebraicTypeTheory.Theories.boolalg))","category":"page"},{"location":"generated/theories/monoid/#","page":"Monoid","title":"Monoid","text":"EditURL = \"https://github.com/kris-brown/AlgebraicTypeTheory.jl/blob/master/docs/literate/theories/monoid.jl\"","category":"page"},{"location":"generated/theories/monoid/#Monoid-1","page":"Monoid","title":"Monoid","text":"","category":"section"},{"location":"generated/theories/monoid/#","page":"Monoid","title":"Monoid","text":"if isdefined(@__MODULE__, :LanguageServer)\n    include(\"../../../src/AlgebraicTypeTheory.jl\")\nend\n\nusing AlgebraicTypeTheory","category":"page"},{"location":"generated/theories/monoid/#","page":"Monoid","title":"Monoid","text":"print(render(AlgebraicTypeTheory.Theories.monoid))","category":"page"},{"location":"#AlgebraicTypeTheory.jl-1","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"","category":"section"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"So far, based on this tutorial and this paper by Jonathan Sterling.","category":"page"},{"location":"#Goals-1","page":"AlgebraicTypeTheory.jl","title":"Goals","text":"","category":"section"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"[x] To experiment with ideas that might be useful for Catlab.jl.\n[x] To construct theories, which are collections of sort declarations, (term) operation declarations, and equality axioms (between sorts and/or terms).\n[x] To instantiate theories using Julia types and functions, so that terms of the theory can be concretely evaluated.\n[ ] To use a theory to rewrite terms of that theory in a normal form.\n[ ] To represent homomorphisms between theories and to be able to compose these to get new instances from old ones.\n[ ] To look at the structure of some theories and automatically infer some natural morphisms (e.g. an injection from a strictly smaller theory).\n[ ] To organize a collection of theories into a queryable knowledge base.\n[ ]To use macros to make the writing of equations/theories more convenient. E.g.","category":"page"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"   App(:mul, [\n      App(:mul, [\n         App(:mul, [\n               App(:mul, [\n                  App(:mul,[\n                     App(:id),\n                     X]),\n                  Y]),\n               Z]),\n         App(:id)]),\n      X])","category":"page"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"could be written as @term (((((id() * X) * Y) * Z) * id()) * X)","category":"page"},{"location":"#Status-1","page":"AlgebraicTypeTheory.jl","title":"Status","text":"","category":"section"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"Theories: implementations for Boolean algebras, preorders, monoids, categories, an algebraicized Martin-Löf type theory (not complete yet).","category":"page"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"Current roadblock: in order to apply rewrite rules to an expression, we need to be able to infer its sort and the sorts of its subterms. This is done by simple pattern matching of expressions: an declaring an operation involves declaring a result sort pattern and term patterns for each argument - by matching terms, we can plug in to the sort pattern and get the result (also effectively typechecking all terms). However, the structure of a term is itself modulo the rewrite rules of the theory, so if there are rewrite rules on sorts or rewrite rules that change the structure of the sort of a term, then things that should be valid arguments will fail to pattern match. As of yet the only theory considered that cannot be fully formalized is the Dependent Types / Categories with Families example.","category":"page"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"To address this, a rewriting algorithm needs to be implemented. Currently, we can rewrite a term by applying a particular rewrite rule at a particular point in the term graph, but what's needed is an algorithm which searches of the rules of a theory and repeatedly applies rewrite rules to get to a normal form (ideally the rewrite system is terminating and confluent).","category":"page"},{"location":"#Overview-1","page":"AlgebraicTypeTheory.jl","title":"Overview","text":"","category":"section"},{"location":"#Terms,-Patterns,-Rewrite-rules-1","page":"AlgebraicTypeTheory.jl","title":"Terms, Patterns, Rewrite rules","text":"","category":"section"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"Take the theory of categories and create a term: Var(:f,Sort(:Hom,[Var(:A,Ob),Var(:A,Ob)])) (using Ob=Sort(:Ob))","category":"page"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"<style>\n.iframe li {\n  width: 100% !important;\n  height: 525 !important;\n}\n</style>\n\n<iframe id=\"igraph\" style=\"border:none;\" seamless=\"seamless\" src=\"https://web.stanford.edu/~ksb/docs/f.html\" height=\"525\" width=\"100%\"></iframe>","category":"page"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"We can define composition by providing the output sort, Sort(:Hom,[Var(:X,Ob),Var(:Z,Ob)]). Here the variables actually are meant to be wildcards, so we can create a new symbol in our graph to mean \"something (arg #2) of a certain sort (arg #1)\" and let the \"something\" be matchable with anything.","category":"page"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"<iframe id=\"igraph\" style=\"border:none;\" seamless=\"seamless\" src=\"https://web.stanford.edu/~ksb/docs/homxzpat.html\" height=\"525\" width=\"100%\"></iframe>","category":"page"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"The variable names were significant (note each wildcard has a name) since these names can be bound in the arguments of the declaration of composition, which are Var(:m,Sort(:Hom,[Var(:X,Ob),Var(:Y,Ob)])]) and Var(:n,Sort(:Hom,[Var(:Y,Ob),Var(:Z,Ob)])]) (the variable names m and n only matter for printing out the operator declaration, and all that was important for Y was that it was the same the two arguments). Now we can compute the sort of arbitrary expressions that match this pattern. So using a theory we can \"upgrade\" a term like App(:cmp,[App(:id,[Var(:A,Ob)]), Var(:f,Sort(:Hom,[Var(:A,Ob),Var(:B,Ob)]))]):","category":"page"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"<iframe id=\"igraph\" style=\"border:none;\" seamless=\"seamless\" src=\"https://web.stanford.edu/~ksb/docs/idf.html\" height=\"525\" width=\"100%\"></iframe>","category":"page"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"...to a \"sorted version\":","category":"page"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"<iframe id=\"igraph\" style=\"border:none;\" seamless=\"seamless\" src=\"https://web.stanford.edu/~ksb/docs/idfinferred.html\" height=\"525\" width=\"100%\"></iframe>","category":"page"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"We can then create pattern out of this and f by itself to make a rule: Rule(\"⋅ left-identity\", f, App(:cmp, [idA,f])) which can perform the left rewrite identity on any graph term of an identity composed with something.","category":"page"},{"location":"#Example-theory-1","page":"AlgebraicTypeTheory.jl","title":"Example theory","text":"","category":"section"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"Sort declarations, term operation declarations, and axioms all can be rendered in plain text, and sorts/terms/patterns may as viewed as term graphs. For example, this fragment of categories with families + dependent types.","category":"page"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"\n################################\n# ******* Theory: cwf ******* #\n################################\n\n4 sorts, 13 ops, 14 rules\n\n#########\n# Sorts #\n#########\n\n==================================================\n\n---------   Ctx\nCtx  sort\n\nContexts: Concretely, a mapping xᵢ:Xᵢ of free variables to types.\nConsider these as objects in a category C.\n\n\n==================================================\n   Γ:Ctx\n-----------   Ty\nTy(Γ)  sort\n\nThe sort of types in context Γ\n\n\n==================================================\n A,B:Ctx\n---------   Hom\nA→B  sort\n\nSubstitutions between contexts: concretely, a substitution bᵢ:βᵢ↦aᵢ:αᵢ.\nConsider these as morphisms in the category C.\n\n\n==================================================\nA:Ty(Γ)  Γ:Ctx\n--------------   el\n𝐄𝐥(Γ⊢A)  sort\n\nThe sort of terms of type A (in ctx Γ), where A is of size α\n 'This is to fix a dependent presheaf El: Psh(ctx)/Ty, i.e. a nat. trans. π: El→Ty'\n\n\n##############\n# Operations #\n##############\n\n==================================================\nA:Ty(Γ)  Γ:Ctx\n--------------   ext\n (Γ.A) : Ctx\n\nContext compreshension operation\n\n\n==================================================\nB:Ty((Γ.A))  A:Ty(Γ)  Γ:Ctx\n---------------------------   Pi\n      Π(A,B) : Ty(Γ)\n\nΠ formation\n\n\n==================================================\n   A:Ctx\n-----------   id\nid(A) : A→A\n\nThe identity morphism\n\n\n==================================================\nγ:Δ→Γ  A:Ty(Γ)  Γ,Δ:Ctx\n-----------------------   Tyact\n     A[γ] : Ty(Δ)\n\nSubstitution action: apply the substitution γ (of type Δ→Γ) to a some type A (in ctx Γ) to obtain a term of type Δ\n\n\n==================================================\n\n-------   emp\n⋅ : Ctx\n\nThe category C has a terminal object: the empty context\n\n\n==================================================\nγ:Δ→Γ  A:Ty(Γ)  Γ,Δ:Ctx  a:𝐄𝐥(Γ⊢A)\n----------------------------------   Elact\n        a[γ] : 𝐄𝐥(Δ⊢A[γ])\n\nSubstitution action: apply the substitution γ (of type Δ→Γ) to a term of type A (in ctx Γ)\nResult: a term of type A[γ] (in ctx Δ)\n\n\n==================================================\nB:Ty((Γ.A))  A:Ty(Γ)  M:𝐄𝐥((Γ.A)⊢B)  Γ:Ctx\n------------------------------------------   lam\n           λ(M) : 𝐄𝐥(Γ⊢Π(A,B))\n\nΠ introduction\n\n\n==================================================\nγ:Δ→Γ  A:Ty(Γ)  N:𝐄𝐥(Δ⊢A[γ])  Γ,Δ:Ctx\n-------------------------------------   snoc\n           ⟨γ,N⟩ : Δ→(Γ.A)\n\n???\n\n\n==================================================\nB:Ty((Γ.A))  A:Ty(Γ)  M:𝐄𝐥(Γ⊢Π(A,B))  N:𝐄𝐥(Γ⊢A[id(Γ)])  Γ:Ctx\n-------------------------------------------------------------   app\n                𝐚𝐩𝐩(M,N) : 𝐄𝐥(Γ⊢B[⟨id(Γ),N⟩])\n\nPi elimination via application\n\n\n==================================================\nf:A→B  g:B→C  A,B,C:Ctx\n-----------------------   cmp\n      (f⋅g) : A→C\n\nComposition, only defined for pairs of morphisms that match head-to-tail, is an associative operation which picks out a third.\n\n\n==================================================\n    Γ:Ctx\n--------------   empsubst\n!(Γ) : Γ→emp()\n\nSubstitution into an empty context\n\n\n==================================================\nA:Ty(Γ)  Γ:Ctx\n--------------   p\n𝐩(A) : (Γ.A)→Γ\n\nProjection function 'drop'???\n\n\n==================================================\n     A:Ty(Γ)  Γ:Ctx\n------------------------   q\n𝐪(A) : 𝐄𝐥((Γ.A)⊢A[𝐩(A)])\n\nProjection function 'var'???\n\n\n###################\n# Equality Axioms #\n###################\n\n==================================================\n  η:Γ→emp()  Γ:Ctx\n--------------------   ! unique\n!(Γ) = η   : Γ→emp()\n\nSubstitution into an empty context is unique.\n\n\n==================================================\nγ:Δ→Γ  A:Ty(Γ)  N:𝐄𝐥(Δ⊢A[γ])  δ:Ξ→Δ  Γ,Δ,Ξ:Ctx\n----------------------------------------------   Comp comp\n     (δ⋅⟨γ,N⟩) = ⟨(δ⋅γ),N[δ]⟩   : Ξ→(Γ.A)\n\n\n==================================================\nγ:Δ→Γ  A:Ty(Γ)  B:Ty((Γ.A))  M:𝐄𝐥((Γ.A)⊢B)  Γ,Δ:Ctx\n---------------------------------------------------   Lambda Substitution\n λ(M)[γ] = M[⟨(𝐩(A)⋅γ),𝐪(A)⟩]   : 𝐄𝐥(Δ⊢Π(A,B)[γ])\n\n\n==================================================\n      γ:Δ→Γ  A:Ty(Γ)  B:Ty((Γ.A))  Γ,Δ:Ctx\n------------------------------------------------   Pi substitution\nΠ(A,B)[γ] = Π(A[γ],B[⟨(𝐩(A)⋅γ),𝐪(A)⟩])   : Ty(Δ)\n\n\n==================================================\nγ:Δ→Γ  A:Ty(Γ)  a:𝐄𝐥(Γ⊢A)  δ:Ξ→Δ  Γ,Δ,Ξ:Ctx\n-------------------------------------------   Term substitution composition\n   a[(δ⋅γ)] = a[γ][δ]   : 𝐄𝐥(Ξ⊢A[(δ⋅γ)])\n\nThe functor to Fam from C preserves composition of substitutions:\nApplying two substitutions in sequence is the same as applying the composition of the substitutions in C\n\n\n==================================================\nA:Ty(Γ)  Γ:Ctx  a:𝐄𝐥(Γ⊢A)\n-------------------------   Term substitution identity\na = a[id(Γ)]   : 𝐄𝐥(Γ⊢A)\n\nThe identity substitution on a term yields the same term\n\n\n==================================================\n    A:Ty(Γ)  Γ:Ctx\n----------------------   Ty identity\nA = A[id(Γ)]   : Ty(Γ)\n\nApplying the identity substitution (on ctx Γ) to a type in ctx Γ yields the same type\n\n\n==================================================\nγ:Δ→Γ  A:Ty(Γ)  δ:Ξ→Δ  Γ,Δ,Ξ:Ctx\n--------------------------------   Ty preserves composition\n  A[(δ⋅γ)] = A[γ][δ]   : Ty(Ξ)\n\nThe functor to Fam from C preserves composition of substitutions:\napplying two substitutions in sequence is the same as applying the composition of the substitutions in C\n\n\n==================================================\nγ:Δ→Γ  A:Ty(Γ)  N:𝐄𝐥(Δ⊢A[γ])  Γ,Δ:Ctx\n-------------------------------------   Universal property of 𝐩\n      γ = (⟨γ,N⟩⋅𝐩(A))   : Δ→Γ\n\n\n==================================================\nγ:Δ→Γ  A:Ty(Γ)  N:𝐄𝐥(Δ⊢A[γ])  Γ,Δ:Ctx\n-------------------------------------   Universal property of 𝐪\n   N = 𝐪(A)[⟨γ,N⟩]   : 𝐄𝐥(Δ⊢A[γ])\n\n\n==================================================\nf:A→B  g:B→C  A,B,C,D:Ctx  h:C→D\n--------------------------------   ⋅ associativity\n ((f⋅g)⋅h) = (f⋅(g⋅h))   : A→D\n\n\n==================================================\n   f:A→B  A,B:Ctx\n---------------------   ⋅ left-identity\nf = (id(A)⋅f)   : A→B\n\n\n==================================================\n   f:A→B  A,B:Ctx\n---------------------   ⋅ right-identity\nf = (f⋅id(B))   : A→B\n\n\n==================================================\n            A:Ty(Γ)  Γ:Ctx\n---------------------------------------   𝐩𝐪 property\nid((Γ.A)) = ⟨𝐩(A),𝐪(A)⟩   : (Γ.A)→(Γ.A)","category":"page"},{"location":"#Computing-with-GATs-1","page":"AlgebraicTypeTheory.jl","title":"Computing with GATs","text":"","category":"section"},{"location":"#","page":"AlgebraicTypeTheory.jl","title":"AlgebraicTypeTheory.jl","text":"We can define an instance of a theory by mapping (possibly parameterized) types to sorts and functions to the term operations.","category":"page"}]
}
