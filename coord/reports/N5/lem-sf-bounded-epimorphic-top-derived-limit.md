## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleBoundedEpimorphicTopDerivedLimit` states
`AlgebraicGeometry.Scheme.ProEt.bounded_epimorphic_top_derivedLimit`, with its sole
proof `sorry`. It introduces no definition, helper theorem, or axiom. The node is
unchanged except for its `lean` record. There is no statement dispute or correction.

Source read: `literature/stacks-project/sites-cohomology.tex`, Tag 0947,
`proposition-enough-weakly-contractibles`, lines 13801–13935, including assertions
(4)–(7) and the displayed five-term cohomology sequence in the proof of (6) and
(7). Exact products identify the product cohomologies; the epimorphic-tower
assertion kills the cokernel in degree b+1. The theorem docstring carries all
five proof steps of this node, including the projection-compatible identification
for the arbitrary supplied product and the cancellation at the upper endpoint.

Hypotheses and clauses, matched to the declaration:

- The arbitrary scheme is `(X : Scheme.{t})`; its unchanged small pro-etale site
  is `X.ProEt` with `topology X`. No affineness, finiteness, nonemptiness, or
  weak-contractibility hypothesis on X is added.
- The sheaf of commutative rings is `(R : Sheaf (topology X)
  RingCat.{max u (t + 1)})` together with `_hcomm`, which says
  `∀ U : X.ProEtᵒᵖ, ∀ r s : R.obj.obj U, r * s = s * r`.
  This is sectionwise commutativity of the supplied ring operations, so neither
  a second ring structure nor a second module action is chosen. A sheaf of
  commutative rings is exactly this data: the ring-hom restriction maps already
  preserve the same operations. In particular no noncommutative coefficient
  case is silently added to this node's statement.
- Module sheaves are the recorded `ringedSiteModules.{max u (t + 1)} R`.
  The coefficient universe is allowed to be arbitrarily large via `u`, and is
  at least the object universe `t+1` of this site's size convention; its
  morphism universe remains `t`. The existing large-universe sheafification
  instances give the abelian structure without a further hypothesis.
- The strict tower is `P : ℕ → CochainComplex ... ℤ` with
  `τ : ∀ n : ℕ, P (n + 1) ⟶ P n`. Here Lean level n represents source level
  n+1. These are actual chain maps, not arbitrary derived morphisms. This
  family presentation is one of the two equivalent presentations explicitly
  given by def-weil-inverse-system; `Functor.ofOpSequence τ` is its recorded
  functor presentation.
- The chosen localization size is `[HasDerivedCategory.{w} ...]`, as in
  def-weil-abstract-derived-category. `DerivedCategory.Q.{w}` is Q.
- The product appearing in the supplied triangle is represented by
  `[HasProduct (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (P n))]`.
  This is the product already required by the node's Roos triangle, with no
  countable-products assumption imposed on other families. The instance can
  be any product witness; the hypothesis and conclusion quantify over it.
- The arbitrary supplied derived limit is `L : DerivedCategory ...`, with
  `_hL : IsDerivedLimit (K := fun n ↦ DerivedCategory.Q.obj (P n))
    (fun n ↦ DerivedCategory.Q.map (τ n)) L`.
  The recorded definition expands to existence of p and δ making the triangle
  distinguished. Its middle arrow is exactly `𝟙 _ - towerProductShift ...`,
  where the shift's nth projection is the next projection followed by Q(τ n).
  Thus no chosen mapping cone or canonical uniqueness is assumed.
- The endpoints and their order are `(a b : ℤ)` and `_hab : a ≤ b`.
- The common vanishing hypothesis is `_hP : ∀ (n : ℕ) (j : ℤ),
  j < a ∨ b < j → IsZero ((P n).homology j)`. Over integers the disjunction
  says exactly j is outside [a,b]. `homology` on an integer cochain complex
  is its cohomology, not its terms or its homological reindexing.
- Epimorphy on the top cohomology sheaves alone is
  `_htop : ∀ n, Epi (HomologicalComplex.homologyMap (τ n) b)`.
  This is a categorical epimorphism of module sheaves, not the stronger
  sectionwise surjectivity condition. No `Epi (τ n)` is required.
- The sole conclusion is `∀ j : ℤ, j < a ∨ b < j →
  IsZero ((DerivedCategory.homologyFunctor ... j).obj L)`. This is precisely
  the stated vanishing on the same interval [a,b], including exclusion of
  b+1. The cochain and derived cohomology functors agree by the recorded
  `DerivedCategory.homologyFunctorFactors`, so the two vanishing expressions
  and the top cohomology maps use the same cohomology as the source.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom` (local-affine locally ringed spaces and their morphisms).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and
  `Scheme.ProEt.topology` (weakly etale objects over X with the pro-etale topology).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent abbreviation of Mathlib's `SheafOfModules`; the latter's
  structure, linear morphisms, and abelian instance were also read.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`, the
  specialization of `HomologicalComplex` to `ComplexShape.up ℤ`.
- `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence` and
  `NatTrans.ofOpSequence`; the node explicitly permits the family presentation.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`; `HomologySequence` supplies
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimit` and `IsDerivedLimitTriangle`, with the full
  signatures and bodies read. Its imported
  `WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism` supplies
  `towerProductShift` and `towerTransitionEndomorphism`, whose bodies and
  projection equations were read.
- `Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit` supplies the
  already published large-coefficient `surjectiveTower_hasSheafify` and
  `surjectiveTower_wEqualsLocallyBijective` instances needed for the statement
  to use the abelian category. Its stronger degreewise-epimorphic tower theorem
  is not used as a hypothesis or substituted for this node.

Proof dependencies are imported: `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`
(`Scheme.ProEt.products_derived`); `Mathlib.CategoryTheory.Limits.Shapes.Products`
(the product universal property); `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
(`HomologySequence.δ`, `exact₁`, `exact₂`, `exact₃`, also needed publicly for the
statement); `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit` (publicly
needed for the statement); and
`Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic`
(`AlgebraicGeometry.ProEtale.milnor_epimorphic`, first conjunct only). The actual
signatures and docstrings of both pro-etale proof dependencies were read. They
apply to arbitrary ring sheaves at these same coefficient universes.

Edge cases checked mathematically against the full signature:

- a=b retains a single cohomological degree; the b+1 endpoint is still killed
  by the top epimorphy hypothesis.
- Negative a or b and arbitrary integral j are included without a natural-degree
  restriction.
- The zero tower, zero coefficient ring, and empty scheme are admitted. No
  nonzero, nontrivial, inhabited, or nonempty assumption occurs.
- There is no empty-index issue: the source tower has all positive levels,
  equivalently ℕ, and the initial transition is retained by the n↦n+1 indexing.
- Only cohomological bounds are assumed: the complexes can be termwise
  unbounded and the τ n need not be degreewise epic.
- Without top epimorphy, coker(1-T_b) can survive in degree b+1, which explains
  why the endpoint hypothesis is material; the weaker [a,b+1] conclusion has
  not been substituted.
- A different product witness or different derived-limit triangle is covered
  by the arbitrary instance and `IsDerivedLimit` witness, respectively.

Searches actually run:

- `msearch.py`, LeanFinder: "A derived inverse limit of a uniformly bounded
  tower of proetale sheaf complexes with epimorphic top cohomology has the same
  bounds". Eight results, principally `LightCondensed.epi_π_app_zero_of_epi`,
  coherent-topology sequential limits, and profinite projections. None states
  this cohomological bound for arbitrary pro-etale ring-sheaf complexes.
- `msearch.py`, Loogle: `"IsDerivedLimit", "homology"`: zero hits.
- `msearch.py`, grep: `[Mm]ilnor|[Rr]oos|derived[Ll]imit|derived_limit`, restricted
  to Mathlib `Algebra/Homology`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`: `IsDerivedLimit` and the
  combinations of `bounded` and `derivedLimit`; then inspected
  `ProEtaleContinuousCohomologyLimit`, `ProEtaleSurjectiveTowerDerivedLimit`,
  `RoosConeCalculus`, `FiniteMittagLeffler`, and the private
  `bounded_of_roos_triangle` in `PointSectionsIntegralCohomologyControl`.
  The last only concludes finite cohomological support and assumes preservation
  of products; the other candidates concern degree-zero sheaf towers, finite
  abelian groups, or Roos compatibility. None is this statement.
- The exact node-id search in `lean/WeilConjectures` and the corresponding
  `dag/lean_names_upstream.json` search found no recorded existing declaration.
- Searches for `Sheaf ... CommRingCat` and commutative-ring sheaf composition
  located existing presentations using `sheafCompose`; the direct sectionwise
  commutativity binder here needs no new notion or duplicated definition.

Validation: every variable and universe is explicitly bound, `autoImplicit` is
false, all source lines are at most 100 characters, and the single theorem has
only `sorry` for its proof. The first server compile exposed failure to infer
`IsDerivedLimit`'s family from the mapped transitions; adding its explicit
`K := fun n ↦ DerivedCategory.Q.obj (P n)` argument repaired elaboration without
changing the mathematical statement. All compilation uses `scompile.py`.
The corrected file passed both the sandbox and its final library-module compile
on the server (24.0 s and 10.9 s), with no errors or warnings.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
