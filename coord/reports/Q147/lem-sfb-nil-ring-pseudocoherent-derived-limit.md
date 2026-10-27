## Worker report

The delivery states `ModuleCat.nilRingPseudoCoherentDerivedLimit` in
`Sheaf.RingTheory.NilRingPseudoCoherentDerivedLimit`. Its sole theorem proof is
`sorry`. `ModuleCat.nilRingRestrictedDerivedStep` is a fully defined helper for
restricting the actual varying-ring transitions to the inverse-limit ring; its
value is the existing derived restriction functor applied to `t n`, followed by
the canonical composition comparison. It adds no independent mathematical notion.
No definition data is postponed. The node changes only in `lean`.

Source read: literature/stacks-project/more-algebra.tex,
lemma-Rlim-pseudo-coherent-gives-pseudo-coherent, Tag 0CQF, including its proof;
and derived.tex, remark-functoriality-derived-limit, Tag 0H9J.
The former allows either all levels pseudo-coherent or eventual nilpotent kernels
plus one pseudo-coherent level. This node and declaration use exactly the first
branch. The latter explains that the derived limit and triangle completion are
not canonically chosen.

Hypothesis and conclusion correspondence:

- The size convention is the explicitly declared `universe u`, with rings in
  `CommRingCat.{u}`, modules in `ModuleCat.{u}`, and the existing canonical
  small-Hom derived categories from the imported ordinary-module framework.
  Increasing u accommodates all the sets and rings in question.
- The inverse sequence of commutative unital rings is
  `A : ℕᵒᵖ ⥤ CommRingCat.{u}`. Index n represents the paper's level n+1.
  Its successive unital ring homomorphism is
  `(A.map (homOfLE (Nat.le_succ n)).op).hom`.
- Surjectivity of every transition is `hsurj`.
- Every kernel element being nilpotent is exactly `hnil`: for each n and x,
  transition(x)=0 implies `IsNilpotent x`. No common exponent, nilpotence of the
  whole ideal, or eventual uniform exponent is assumed.
- The ring of compatible tuples with its projections is presented by
  `c : Cone A` and `hc : IsLimit c`; the ring is `c.pt` and the projection is
  `(c.π.app (Opposite.op n)).hom`. Mathlib's CommRingCat limits are constructed
  from compatible tuples with componentwise operations. Allowing any limiting
  cone gives the same ring with projections up to their unique ring isomorphism;
  choosing that concrete cone specializes the declaration exactly to the node.
- The objects in D(A_n) are `K n`; pseudo-coherence at EVERY level is `hpc`,
  using the recorded `DerivedCategory.IsPseudoCoherent` definition verbatim.
- The actual maps K_(n+1) -> Res K_n are `t n` using
  `ModuleCat.derivedRestrictScalars`, the exact functor's `mapDerivedCategory`.
- `ht` says `ModuleCat.IsDerivedBaseChange (t n)`. This existing upstream
  predicate is the universal-arrow formulation of an invertible derived
  scalar-extension adjunct. If F is left adjoint to Res and gamma is the adjunct
  of t, then under adjunction the map g |-> t followed by Res(g) is composition
  with gamma. It is bijective for every target exactly when gamma is invertible
  (Yoneda, or construct the inverse by applying the bijections to identities).
  Thus this is equivalent to the node's condition on the specified map, including
  the unit normalization, not an arbitrary isomorphism of the two objects.
- The restricted tower has objects `derivedRestrictScalars (c.π.app ...).hom |>.obj`
  and transitions `nilRingRestrictedDerivedStep A c K t`. Cone naturality gives
  the ring-map equality used in the existing `derivedRestrictScalarsCompIso`.
  This is the canonical identity-on-elements restriction comparison.
- The displayed `HasProduct` is precisely the product needed for the node's
  Roos-triangle definition, rather than an extra mathematical restriction;
  countable products also exist in these module derived categories.
- An arbitrary specified derived limit is the input L, p, delta and `hlim`.
  `hlim` uses the recorded `CategoryTheory.IsDerivedLimitTriangle`, i.e.
  `Triangle.mk p (1-shift) delta` is distinguished. No particular derived-limit
  functor or preferred triangle is chosen.
- The first conclusion is `DerivedCategory.IsPseudoCoherent L`.
- The second is, for EVERY n, `IsDerivedBaseChange` of the actual composite
  `p ≫ Pi.π ... n`, along the projection ring homomorphism. By the equivalence
  above, the scalar-extension adjunct of precisely that projection is invertible.
  It is neither a mere existence of unrelated isomorphisms nor a statement only
  about one choice of derived limit.
- There are no Noetherian, adic-presentation, flatness, common-exponent, or
  boundedness assumptions added. Bounded-above finite-free representatives appear
  only in the imported definition of pseudo-coherence, as in the source.

Dependency declarations read and used:

- `def-weil-size-convention`: metatheoretic convention record, realized by the
  explicit universe declaration (no Lean object).
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, and localization `DerivedCategory.Q`.
- `def-pc-ring-pseudo-coherent-complex`:
  `WeilConjectures.RingTheory.RingPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`; its finite-free, bounded-above definition
  was read in full.
- `lem-pur-derived-change-of-rings`:
  `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, publicly retaining the
  generic construction and supplying ordinary-module universal pairs and
  `ModuleCat.ordinaryDerivedExtendScalars`. That module publicly imports
  `WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange`, whose
  `ModuleCat.IsDerivedBaseChange`, `derivedRestrictScalars` and
  `derivedRestrictScalarsCompIso` supply the exact existing universal-arrow and
  restriction interfaces used here. This is the dependency's existing ordinary
  module presentation, not a duplicate scalar-extension definition.
- `lem-pur-sheaf-ring-derived-coefficient-adjunction`:
  `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`,
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`, publicly imported for
  its exact restriction and representative-normalized coefficient adjunction.
  The universal-arrow encoding avoids needing a second chosen ordinary-module
  adjunction or an additional assertion about its existence.
- `def-weil-derived-limit`:
  `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`,
  `CategoryTheory.IsDerivedLimitTriangle` (the explicit-witness form of the
  recorded `IsDerivedLimit`).

Recorded proof dependencies with statements are imported without public:
`WeilConjectures.Algebra.Homology.BoundedFlatKFlat`,
`WeilConjectures.RingTheory.FiniteModuleSurjectiveModIdeal`,
`Mathlib.Algebra.Module.Projective`,
`Sheaf.Algebra.Homology.SurjectiveModuleComplexTowerLimit`,
`Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism`, and
`Mathlib.CategoryTheory.Triangulated.Triangulated`. The statement dependencies
that also occur in proof_deps already have public imports.
`lem-sfb-jacobson-marked-free-complex-lift` has no Lean record or mathlib match in
the read repository, so it has no proof import yet. It is needed only for the
future proof, not to type this statement; its exact use remains in the theorem's
six-step proof docstring.

Edge cases checked by reading the source and signature:

- Constant towers, identity transitions and zero kernels are allowed.
- Zero rings and zero complexes are allowed; no Nontrivial or nonzero-rank binder.
- All integers may occur as the upper cutoff in pseudo-coherence, with no common
  cutoff hypothesized for the K_n.
- Nil ideals with no nilpotence exponent satisfy hnil; only elementwise nilpotence
  is used, and there is no global nilpotent-ideal binder.
- Every natural-number level is included after reindexing the source's positive
  integers, including its first level.
- Every p and delta completing the specified Roos triangle are quantified; no
  uniqueness of triangle completions or preferred derived limit is used.

Searches for reuse (2026-10-24):

- msearch.py LeanFinder: "Derived inverse limit of compatible pseudo coherent
  complexes over surjective rings with locally nilpotent kernels is pseudo
  coherent with derived reduction isomorphisms". Eight hits on local cohomology,
  condensed categories and adic completion; no reconstruction theorem.
- msearch.py Loogle: `DerivedCategory, "coherent"`. Zero hits.
- msearch.py grep: `[Pp]seudo[Cc]oherent|[Pp]seudo.coherent|[Dd]erived[Ll]imit`
  in Mathlib/Algebra. Zero hits for this query.
- msearch.py LeanSearch: "Derived inverse limit pseudo coherent complexes
  surjective rings nil kernels reconstruction". Eight hits on generic derived
  localization, direct/inverse limits and short-complex cohomology; no match.
- rg over lean/WeilConjectures and lean/Sheaf for pseudo-coherent limits and this
  blueprint id: no theorem match. Existing ordinary derived scalar extension and
  the universal-arrow predicate were located and reused. Direct searches for both
  proposed full declaration names in Mathlib, WeilConjectures, Sheaf and
  dag/lean_names_upstream.json found no name collision.

No STATEMENT-DISPUTED or source correction is needed. No new DAG nodes or
repaired dependency modules are introduced. Backward definitional-equality
elaboration options are used to unfold constant-functor ring expressions; they
change no mathematical data or hypotheses. All variables are explicitly bound
and autoImplicit is disabled.

## Second reading by Q147

A separate reading pass compared the written node, 0CQF and the final signature.
It checked the polarity of the inverse ring arrow; the orientation of the
restriction-composition comparison; the source and target of each t_n; and the
quantifiers on kernel elements, pseudo-coherence and projections. The limiting
cone supplies the actual projection ring maps. The same p from hlim appears in
every base-change conclusion. The existing universal-arrow predicate is
logically equivalent to the adjunct-isomorphism condition, as explained above;
its use does not assert a noncanonical comparison. No added finiteness, adic,
flatness or uniform-exponent condition was found. Both conclusions and every
node hypothesis are present. The helper is fully defined using the existing
restriction comparison and is included in lean.declarations. No mathematical
mismatch was found; only product-category elaboration annotations were needed.
The maintainer supplies the independent delivery review per the dispatcher brief;
this pass is by the same worker and no second agent was started.
