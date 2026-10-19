## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSheafZeroOnCover` states
`AlgebraicGeometry.Scheme.etaleSheaf_isZero_of_isZero_over_cover`, with a single
`sorry` proof. No definitions or auxiliary theorems are introduced. The node is
unchanged except for its `lean` record.

Hypotheses and conclusion, clause by clause:

- A scheme X is `(X : Scheme.{u})`.
- An arbitrary family of schemes is `(I : Type v) (V : I → Scheme.{u})`.
  The independent index universe allows arbitrary set-indexed families, including
  finite and empty families; neither `Finite I` nor `Nonempty I` is assumed.
- The morphisms to X are `(φ : ∀ i : I, V i ⟶ X)`.
- Every morphism is étale by `[∀ i : I, AlgebraicGeometry.Etale (φ i)]`.
- Joint surjectivity is exactly
  `hcover : ∀ x : X, ∃ (i : I) (y : V i), φ i y = x`.
  This is the pointwise formulation of the union-of-ranges condition in
  `Scheme.ofArrows_mem_smallEtaleTopology_iff`. Thus it is exactly the small
  étale covering condition, with no quasi-compactness or finiteness added.
- The coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`, and the module
  sheaf is `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  This is the fixed-coefficient module-sheaf encoding explicitly authorized
  by the recorded `def-weil-pbc-etale-sheaves`; it uses the same module-value
  universe as the six-functor/constructible-sheaf material. There is no
  torsion, constructibility, finiteness, or nonzero-ring hypothesis.
- The restriction on the slice at V_i is literally
  `F.over (Scheme.Etale.mk (φ i))`. `Sheaf.over` lands on
  `X.smallEtaleTopology.over (Scheme.Etale.mk (φ i))`; its underlying
  presheaf is composition with `Over.forget`, so on a slice object W → V_i
  the section module is F(W), as the node requires. No comparison with
  scheme inverse image is assumed.
- The local vanishing assumption is
  `hzero : ∀ i : I, IsZero (F.over (Scheme.Etale.mk (φ i)))`.
- The conclusion that F is the zero sheaf is `IsZero F`.
- The node's open-immersion cover is an example, not an additional
  hypothesis or conclusion. Open immersions are étale, hence included.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, for schemes and their category.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  for the example in the node; it adds no hypothesis.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`,
  `Scheme.ofArrows_mem_smallEtaleTopology_iff`; the underlying category is
  `Scheme.Etale`, constructed with `Scheme.Etale.mk` from
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the recorded dependency
  module, read using `scompile.py --source` because it is not in the old
  source checkout. Its node's mixed record explicitly retains Mathlib
  `Sheaf`/`ModuleCat` as the fixed-coefficient encoding used here; the
  set-valued predicates in that file are not substituted for module sheaves.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`, the full
  subcategory defined by the sheaf condition.
- `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`,
  `GrothendieckTopology.overPullback`, `Sheaf.over`, for actual slice restriction.
- Proof-only imports: `Sheaf.CategoryTheory.RingedSiteModules`
  (`CategoryTheory.ringedSiteModules`, a transparent abbreviation of Mathlib
  `SheafOfModules`), `Sheaf.CategoryTheory.SiteCoveringAxioms`
  (`CategoryTheory.Precoverage.IsSiteForCoverings`), and
  `Mathlib.CategoryTheory.Sites.Sheaf`. These are the recorded modules of
  the node's four proof dependencies; the abelian-sheaf dependency uses
  `Sheaf` on the recorded small étale topology.

Edge cases checked mathematically before writing:

- I empty: joint surjectivity forces X empty. Every test object over X is
  empty and has an empty cover. The sheaf axiom forces its module of
  sections to be terminal, hence zero. The local hypothesis is vacuous
  and the conclusion is true; no nonemptiness restriction was inserted.
- X empty with a nonempty cover: all covering and test objects are empty,
  and the same empty-cover sheaf axiom applies.
- Identity cover: restriction to the terminal object of the site recovers
  F on the equivalent slice, and the hypothesis is exactly its vanishing.
- F zero, zero coefficient ring, infinite covers, finite open covers,
  and non-open étale covers all satisfy the stated generality.
- No separation, Noetherian, finite-dimensional, or affine assumption is used.

Searches (run through `msearch.py Q42 lem-sf-sheaf-zero-on-open-cover`):

- LeanFinder: “An etale sheaf of modules is zero if its restrictions to every
  member of a jointly surjective covering family are zero”. Eight hits;
  `Scheme.zero_of_zero_cover` only treats individual sections of the
  structure sheaf on an open cover, and local-generator hits do not state
  this result. No exact match.
- Loogle: `SheafOfModules.overFunctor, IsZero`. Zero hits, with unknown
  identifier `IsZero` reported by the service. Not used as evidence that
  the zero-object API is absent.
- Mathlib grep: `isZero.*(cover|over)|zero_of.*cover|overFunctor` in
  `Algebra/Category/ModuleCat`. Five hits, all the slice restriction API
  in `Sheaf/PushforwardContinuous.lean`; no zero-detection theorem.
- LeanSearch: “A sheaf of modules is a zero object if it restricts to zero
  on a covering family”. Eight hits, including `Scheme.zero_of_zero_cover`,
  `ModuleCat.isZero_iff_subsingleton`, and generic module-sheaf declarations;
  none gives this étale slice-cover theorem.
- `rg` in the upstream `WeilConjectures/` and project `lean/Sheaf/` for
  `isZero.*cover|isZero_of.*over|zero_of.*cover` found scheme/Zariski
  module vanishing statements and unrelated formal-completion results.
  None states vanishing of an étale module sheaf from slice restrictions
  on an arbitrary jointly surjective étale family.
- Searched the item id in upstream sources and the proposed full theorem
  name in Mathlib, upstream, `lean/Sheaf/`, and `dag/lean_names_upstream.json`:
  no occurrence of the proposed declaration and no upstream attachment.

Source checked: the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/thm-sf-hom-ctf.proof.md`,
whose first and last sentences assert exactly the locality expanded in
this node's three proof steps. The base node's `source.place` says “Step 5”,
but the source has unnumbered paragraphs; this inherited citation issue is
already noted in its stage-1 review. The theorem docstring cites the actual
first and last sentences and carries all three natural-language proof steps.
No mathematical statement fault or dispute was found.

## Second reading by Q42

This is the worker's self-check; the maintainer supplies the independent
review, as required by the dispatcher brief. I reopened the node and the
module and checked the family, étaleness, pointwise covering, module-sheaf
category, literal slice restriction, local `IsZero`, and global `IsZero`
clause by clause. The arbitrary index type retains the empty and infinite
cases. In particular, I checked `Sheaf.over` and `overPullback` in Mathlib
rather than replacing slice restriction by an unrecorded scheme-pullback
identification. The proof docstring covers pullback of the cover,
separatedness, and the zero-object conclusion. There are no new nodes,
dependency repairs, statement corrections, or proofs beyond `sorry`.
