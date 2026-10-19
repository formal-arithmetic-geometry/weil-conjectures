## Worker report

Q139 states `lem-per-adic-heart-pullback-fibres` in
`Sheaf.Paper.AdicHeartPullbackFibres`, declaration
`AlgebraicGeometry.Scheme.PerAdic.adicHeartPullbackFibres`. The original node statement,
proof and proof dependencies are unchanged. Its statement dependencies gain the already
recorded stratification, coherent scalar-extension and functor-descent nodes used in the
signature. No independent missing notion or dependency replacement is introduced.

The definitions construct the normalized functors; the six supporting theorems and the
main theorem have `sorry` proofs. No definition contains `sorry`. Choices of t-structures
are fixed by their classes, the geometric fibre is uniquely fixed by its composite with
rationalization, and the pullback family is uniquely fixed by its finite-stage functors
and the actual completed scalar comparison (`PbcPullbackBetaSpec`). There is no assumed
fibre functor, freely chosen comparison, or additional completion convention.

Hypotheses and objects:

- `k : Type u`, `[Field k]`, `l : ℕ`, `[Fact l.Prime]`, and
  `[Fact (IsUnit (l : k))]` render the arbitrary base field and invertible prime.
- `Base k` bundles a scheme with its `Over (Spec (.of k))` structure and
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on that structure morphism.
  Thus `V T : Base k` are exactly separated finite-type k-schemes. The morphism
  `h : V.scheme ⟶ T.scheme` is an arbitrary scheme morphism: k-linearity is not added.
  `base_properties` and `base_geometric_properties` derive the noetherianity,
  finite dimension and local invertibility needed by the recorded category interfaces;
  these are conclusions of the geometric hypotheses, not extra hypotheses.
- `Qbar : Type v`, `[Field Qbar]`, `[Algebra (Padic l) Qbar]`, and
  `[IsAlgClosure (Padic l) Qbar]` are the fixed algebraic closure. The finite stage is
  `L : Padic.FiniteCoefficientFields l Qbar`; its coefficient field is the existing
  `pbcFiniteField.{u} l Qbar L`, the small model of the actual intermediate subfield.
  `stageEmbedding` is its actual embedding in Qbar, using `Shrink.algEquiv` and the
  subfield inclusion. It is not a new independent coefficient field.
- All finite derived objects are in `PbcRationalCategory` of the actual
  `pbcIntegralDatum` and `pbcUniformizer`. Common-stage objects are in
  `pbcQbarCategory`. Integral objects retain their derived-complete and compatible
  étale-origin conditions through `PbcBoundedConstructibleComplete`.
- Geometric points are exactly `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]` with a map
  `Spec (.of Ω) ⟶ W.scheme`. Their underlying points use `SpecToEquivOfField`.
  The coefficient closure universe v is independent of the scheme universe u;
  common-stage fibre modules have universe `max (u+1) v`.

Clause correspondence:

1. `rationalT` selects the t-structure in `pbc_localized_tstructure`.
   `RationalStandardAssertions` states boundedness and the three equivalences for
   the aisle, coaisle and heart: each is exactly an isomorphism to the rationalization
   of an integral object in that integral class. Both directions are present.
   `Heart` is the actual full t-heart, rather than a second constructible category.
2. `cohomology t r` is literally `t.truncLE r ⋙ t.truncGE r ⋙ shiftFunctor _ r`.
   The natural cohomology/rationalization isomorphism and the identification of integral
   cohomology with `DerivedCategory.singleFunctor _ 0` of ambient
   `DerivedCategory.homologyFunctor _ r` give precisely the stated degree-zero formula.
   The last clause of `RationalStandardAssertions` allows any integral representative
   whose off-zero ambient cohomology identities are killed by some uniformizer power.
   It does not require those integral cohomology objects themselves to vanish.
3. `commonClass` is the isomorphism closure of the finite-stage aisle/coaisle.
   `commonT_existsUnique` states the indexed class equalities and boundedness;
   `commonT` is this uniquely determined t-structure. `CommonStandardAssertions`
   identifies its heart with finite-stage heart representatives and gives natural
   comparisons for upper/lower truncation and every cohomology degree through
   every finite-stage inclusion. `ScalarAssertions` gives the corresponding natural
   comparisons for every finite extension, including identity extensions.
4. `rationalPull` is `pbcConditionalRational` applied to
   `pbcActualCompletedPull`, with `integralPull_mem` supplying its constructible
   restriction. `pullFamily` retains this functor at every finite field and the
   canonical completed scalar comparison, not an arbitrary natural isomorphism.
   `commonPull` is its actual `StageSystem.Morphism.functor`, including the beta/pullback/
   beta-inverse representative formula. `RationalPullAssertions` and
   `CommonPullAssertions` state its shift comparison, triangulated exactness and
   preservation of both indexed standard halves. In particular it preserves the hearts;
   bounded t-exactness also gives the asserted exact restriction to the hearts.
5. `integralFiber` is the integral inclusion, actual completed geometric pullback,
   ambient degree-zero cohomology, point sections, and extension from the actual
   lifted integer ring to E. `integerToField` is the genuine ring inclusion.
   `fiber_existsUnique` states its unique descent through raw rationalization,
   and `fiber` is that descent. `heartFiber` is its restriction to the actual heart.
   Thus its action on arrows is fixed as well as its action on objects.
6. `integralLimitFiber` uses the strict `completedReductionTower`, takes the degree-zero
   module tower, evaluates at the final geometric pro-étale object, forms its actual
   inverse limit and then extends scalars to E. `RationalLimitAssertions` identifies
   this functor naturally with `integralFiber`. On a lisse integral stratum the retained
   compatible étale origins identify these finite quotients and transition maps with
   the finite étale fibres of `lisseIntegralFiber`; coefficient inversion is exactly
   the prescription of `lisseRationalFiber`. No discrete non-torsion étale coefficient
   sheaf is used. This normalization applies also to complexes presenting heart objects
   only after rationalization.
7. `RationalFiberAssertions` states preservation of finite limits and finite colimits
   (exactness) and joint reflection of isomorphisms of heart morphisms.
   `CommonFiberAssertions` states these same properties on the common-stage heart.
8. `RationalComparisonAssertions` gives the natural isomorphism
   `rationalPull h ⋙ fiber v ≅ fiber (v ≫ h)`. It also states isomorphism of fibres
   of a heart object at any two geometric lifts of the same underlying point,
   without asserting a canonical choice of that latter isomorphism.
9. `ScalarFiberAssertions` gives natural finite-extension/fibre comparisons.
   `ScalarPullbackFiberAssertions` states an explicit componentwise commuting square
   between pullback-fibre comparisons, finite scalar comparisons, and the canonical
   beta of the completed pullback family. Both source and target fibre comparisons
   participate in that equation. `CommonFiberNormalization` requires Qbar-linearity
   and natural identification of every finite-stage restriction with its actual
   finite-stage fibre extended to Qbar. The common pullback comparison in
   `CommonFiberAssertions` comes with the explicit finite-stage component square
   using `pullInclusionIso`, so it is compatible with the same actual pullback.
10. `RationalSupportAssertions` supplies an existing
    `FiniteLocallyClosedStratification`, the local finite-free condition `LisseStrata`,
    a rank function locally constant after every stratum immersion, and equality
    of its values with the finite dimension of every geometric fibre. It concludes
    `Topology.IsConstructible {x | rank x ≠ 0}`. Since every fibre is finite dimensional
    over a field, this is exactly the nonzero-fibre locus. The last clause of
    `CommonFiberAssertions` supplies the same data with a finite-stage lisse model,
    Qbar dimensions and the identical constructible nonzero-rank condition.

`rationalLE`, `rationalGE`, `rationalTruncLE`, `rationalTruncGE` and
`rationalCohomology` are explicit adapters to the recorded localized t-structure.
They fix the relevant shift instance when the same raw category is also displayed as a
finite stage of the scalar system; they neither impose equality of independently chosen
shift structures nor change a t-class, truncation, cohomology object or category.

Dependency declarations used:

- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcRationalization`,
  `PbcIntegralRing`, `pbcCompletedSection` and the actual integral full subcategory.
- `Sheaf.Paper.PbcQbarCategory`: `pbcQbarCategory`, with `pbcStageCategory`,
  `pbcFiniteField` and `pbcScalarSystem` reexported from its recorded diagram.
- `Sheaf.Paper.IntegralTStructure`: `pbcIntegralTStructure`.
- `Sheaf.Paper.LocalizedTStructure`: `pbc_localized_tstructure`.
- `Sheaf.Paper.PbcActualStrictPullback`: `pbcActualCompletedPull` and the strict tower
  comparison; `completedReductionTower` is the actual strict finite-reduction functor.
- `Sheaf.Paper.PbcScalarExtension`: `pbcConditionalRational`,
  `pbcFiniteFieldInclusion` and the coherent scalar system interfaces.
- `Sheaf.Paper.PbcDescentFunctors`: `PbcPullbackBetaSpec` and the actual
  `StageSystem.Morphism` functor with `ιCompFunctorIso`.
- `Sheaf.Paper.LisseAdicSheaves`: the recorded `LisseIntegralSheaf`,
  `lisseIntegralFiber` and `lisseRationalFiber` prescribe the retained étale-origin
  interpretation of the strict-limit fibre. This is not a replacement category for
  the derived constructible heart.
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`:
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`, using its current
  recorded interface without an extra constructibility hypothesis on each stratum.
- Mathlib: `Triangulated.TStructure` and its actual heart and truncations;
  `DerivedCategory.homologyFunctor`; `IsAlgClosed`, `SpecToEquivOfField`;
  `Topology.IsConstructible`; `ModuleCat.extendScalars`, `restrictScalars`,
  `SheafOfModules.evaluation`, `SheafOfModules.free`, functor whiskering and limits.
- The scheme-properties dependency is a convention node. Its `LocallyOfFiniteType`,
  `QuasiCompact`, separatedness and scheme-over-base conventions are used directly.

All already recorded proof-dependency modules are imported privately; modules whose
interfaces occur in the statement are imported publicly. The main theorem docstring
contains the source-based proof plan, with the completion, rationalization, bounded
truncation, finite-level étale comparison, exactness and rank arguments.

Edge cases checked by reading the types and construction:

- Empty schemes and empty strata are permitted; no nonempty or connected hypothesis
  enters `Base`, the coverings, or the finite stratification. A zero object has zero
  rank everywhere and empty constructible support.
- Rank zero is allowed (`Fin 0` in `freeObject`). Different rank loci on a stratum
  are allowed by local constancy; no globally constant rank is imposed.
- All integers, including negative degrees, occur in the truncation/cohomology
  clauses. Torsion away from degree zero is explicitly allowed before rationalization.
- The prime need not be invertible by definition of the category: its unit in k is
  assumed and its units on stalks are derived, with no finite or algebraically closed
  hypothesis on k.
- Identity finite extensions are included (`a : L ≤ L`), as are all later common
  stages. All fields Ω allowed by the recorded geometric-point convention are
  quantified, and two different Ω over one point are covered.
- Pullback is the actual completed functor, even when h is nonflat or not a k-map.
  The proof plan uses local finite-free models, not flatness of the coefficient map.
- The choice-based constructions are determined by equality or by the unique
  localization/normalized descent property used downstream; no undetermined
  existence theorem supplies object data.

Searches for an existing statement (recorded in `searches.jsonl`):

- `msearch.py` LeanFinder, "constructible adic heart pullback geometric fibres":
  eight ordinary scheme-fibre/product hits, no adic-heart statement.
- `msearch.py` LeanSearch, "constructible l adic sheaves geometric fibre exact pullback":
  eight ordinary sheaf/module inverse-image declarations; none states this result.
- `msearch.py` Loogle, `TStructure.heart, Functor.IsTriangulated`: no hits
  (the service did not recognize the abbreviated first identifier).
- `msearch.py` grep, `adic.*heart|heart.*pullback`, Mathlib `CategoryTheory`: no hits.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for the target id:
  no existing declaration. Searches for constructible hearts, pullbacks, fibres,
  t-structures and scalar systems found the dependency interfaces listed above.
  Older `SfConstructibleHeart`/constructible-heart interfaces use different categories
  or hypotheses and do not state this node on its recorded raw Pbc categories.
- The exact dependency declarations, docstrings, and the relevant parts of BS 6.8
  in the repository PDF were read. No statement error or disputed mathematical
  clause was identified. No `STATEMENT-DISPUTED` flag is needed.

Validation: `scompile.py Q139 lem-per-adic-heart-pullback-fibres` compiled the full
module cleanly in both its sandbox and actual module forms under the prescribed
per-file limit. No error or non-sorry warning remains. Delivery preflight and its
additional per-file compilation are run by `deliver2.py --no-push` before delivery.

## Second reading by Q139

No second reading by a worker: this dispatcher-started worker delivers directly and
starts no other agent. The maintainer's independent review is the independent reading.
