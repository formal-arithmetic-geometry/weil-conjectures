## Worker report

Recorded an existing declaration; no Lean module or new theorem is delivered:
`CategoryTheory.Subobject.cokernelOfLEMkIso`, in
`WeilConjectures.ConstructibleSheaf.Devissage`, source lines 56–65. Read its complete
signature, docstring, and construction in the local source and independently in the
current server source returned by `scompile.py --source`.

The mathematical source is the second paragraph of
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-coefficient-heart/sk-lem-coefficient-heart-filtration.proof.md`.
The paragraph obtains an exact sequence on the open-extension objects and identifies
its quotient with the quotient of the represented subsheaves. This declaration performs
exactly that representative-change comparison.

Hypothesis and clause correspondence (node names on the left, declaration names on the right):

- An abelian category C: specialize `{C : Type*} [Category C]` to C with `[Abelian C]`.
  The recorded dependency `def-sp-abelian` is Mathlib's `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`. Its preadditive structure supplies
  `HasZeroMorphisms C`, and its `has_cokernels` field supplies `HasCokernels C`.
  These are consequences of the node's assumption, not additional hypotheses.
  The declaration is already available at the more general level where only these
  consequences are needed. Object and morphism universes are independent.
- Objects A, A', B, M: the declaration binds `A₁, A₁', A₂, B`, respectively.
- Monomorphisms f:A→M and g:B→M: `f₁ : A₁ ⟶ B`, `f₂ : A₂ ⟶ B`,
  `[Mono f₁]`, and `[Mono f₂]`.
- Isomorphism alpha:A≅A': `α : A₁ ≅ A₁'`.
- Map phi:A'→B: `φ : A₁' ⟶ A₂`.
- Equation f=g∘phi∘alpha: `hφ : f₁ = α.hom ≫ φ ≫ f₂`;
  Lean's composition notation lists arrows in the order they are traversed.
- Subobject means an isomorphism class of monomorphisms into M:
  `Subobject M`, defined as `ThinSkeleton (MonoOver M)` in
  `Mathlib.CategoryTheory.Subobject.Basic`; `mk f₁` and `mk f₂` represent the classes.
  The partial order descends factorization of monomorphisms.
- Every proof h:[f]≤[g]: the unrestricted argument `h : mk f₁ ≤ mk f₂`.
- The chosen-representative map iota_h: `Subobject.ofLE (mk f₁) (mk f₂) h`.
  Read `underlying`, `arrow`, `underlyingIso`, `ofLE`, and `ofLE_arrow` in
  `Mathlib.CategoryTheory.Subobject.Basic`. In particular `ofLE_arrow` gives
  `ofLE _ _ h ≫ (mk f₂).arrow = (mk f₁).arrow`, precisely the node's equation;
  uniqueness follows by the monomorphism `(mk f₂).arrow`.
- Conclusion: `cokernel (ofLE _ _ h) ≅ cokernel φ`, with the same orientation.
  Mathlib's `cokernel` is the chosen universal zero cofork, so it implements the
  node's universal quotient. The result supplies an actual isomorphism.
- No strictness or nonzero assumptions: none occur in the signature.

Read also the recorded proof dependencies: `def-weil-pbc-category-colimit` records
`CategoryTheory.Limits.colimit` in `Mathlib.CategoryTheory.Limits.HasLimits`;
`lem-weil-pbc-pushout-cokernel-iso` matches
`CategoryTheory.Limits.isIso_cokernel_map_of_isPushout` in
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels`.
The DAG proof compares representatives by isomorphisms, cancels g to obtain the
commuting square, checks the pushout by composing with the inverse target
isomorphism, and applies this pushout-cokernel comparison. The existing declaration
constructs the identical comparison directly using `cokernelIsoOfEq`,
`cokernelEpiComp`, and `cokernelCompIsIso`. Its reuse requires no replacement imports
or new statement module.

Edge cases checked: equal subobjects and identity inclusions are permitted; then
phi is an isomorphism and both cokernels are zero. A=0 is permitted, giving the
quotient represented by B. The case g=id_M is permitted, as are all zero objects.
No proper inclusion, nonempty type, chosen inequality witness, or size equality
is imposed. The arbitrary h binder covers every proof, as required.

Searches performed with the prescribed msearch.py wrapper:

- LeanFinder: “The cokernel of the inclusion between subobjects represented by
  monomorphisms f and g with f = alpha composed with phi composed with g for an
  isomorphism alpha is isomorphic to the cokernel of phi”. Eight Mathlib hits,
  including `cokernel.mapIso`, `cokernel.ofIsoComp`, and `cokernelCompIsIso`;
  none directly includes the represented-subobject arguments.
- Loogle: `"cokernel", "Subobject"`. One hit,
  `ModuleCat.cokernel_π_imageSubobject_ext`, not the abstract-category comparison.
- Mathlib grep: `cokernelOfLEMkIso|cokernel.*Subobject|Subobject.*cokernel`,
  restricted to CategoryTheory. Six hits concerning the cokernel order map,
  not the complete statement.
- LeanSearch: “The cokernel of an inclusion between subobjects represented by
  monomorphisms f and g with f equal to alpha then phi then g for an isomorphism
  alpha is isomorphic to the cokernel of phi”. Eight hits, including
  `cokernel.mapIso`, `cokernelIsoOfEq`, and `cokernelEpiComp`, no direct match.
- Local rg in `lean/WeilConjectures` for `cokernelOfLEMkIso` found the exact
  declaration in `ConstructibleSheaf/Devissage.lean:56`, plus its use at line 231.
  Broader subobject/cokernel searches found related isomorphic-arrow comparisons
  in ExactCouple/Convergence and filtration modules, not a preferable exact match.
- Local rg in `lean/Sheaf` found a use of that same declaration in
  `Paper/ContinuousConstructibleIntegralGluing.lean:581`; it does not redefine it.
- Grep for the item id in `lean/WeilConjectures` and the declaration name in
  `dag/lean_names_upstream.json` produced no matches. The source declaration and
  the live server source, rather than that older index, establish availability.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED issue.
The requested CompactObject example has been withdrawn to a declaration-free stub;
its node still illustrates the existing-declaration record conventions.

Validation: a scratch consumer imports the existing module and Mathlib Abelian,
binds all object and morphism universes explicitly, and checks the application to
exactly the node's abelian-category signature. The scratch file is not delivered.
The delivery wrapper additionally checks the recorded existing declaration on the
server and runs the required preflight. Independent mathematical review is left
to the maintainer, as instructed for dispatcher-started workers.

The scratch consumer compiled cleanly through scompile.py in both the sandbox and
library checks (4.4 s and 4.6 s). `#print axioms` reported exactly
`[propext, Classical.choice, Quot.sound]` for the existing declaration.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
