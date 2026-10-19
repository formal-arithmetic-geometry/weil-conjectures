## Worker report

Q66 states `lem-pod-derived-automorphism-hom-evaluation` in
`Sheaf.Paper.DerivedAutomorphismHomEvaluation`. The primary declaration is
`WeilConjectures.derivedAutomorphismHomEvaluation`; the node's declaration list
also records the constructions and the separate coherence statements. The mathematical
statement, source, proof, and proof dependencies are unchanged. The already landed
`lem-pur-derived-pullback-tensor-iso` is added to statement dependencies for its canonical
braidings and constructible-stage composition maps; these are reused, not reconstructed.
There are no new nodes or repaired dependency records.

The theorem proofs are all `sorry`. Definitions have real data. Choices of closed or
representative data are made only from named uniqueness theorems: the normalization fixes
all transposes, all Hom product projections, or the derived-functor unit square. No arbitrary
map, arbitrary natural isomorphism, existence-only object, or independent levelwise lift is
used as the comparison.

Hypotheses and every clause of the node are represented as follows.

| Node text | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` |
| Finite E/Qell, its integers and uniformizer | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`; the recorded `Padic.coefficientExtensionIntegers` and uniformizer through the operation dependencies |
| Positive exponent n | An index `n : ℕ` means exponent `n + 1` in `finiteCoefficientRing`; thus exponent one is included and exponent zero is excluded |
| Schemes and isomorphism | `{X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]` |
| Ell invertible on both schemes | Both residue-field `Invertible` families are present in every constructible-stage statement and in the finite statements |
| Small pro-etale sites | `Scheme.ProEt.topology`; object universe `u+1`, morphism universe `u` are retained |
| Arbitrary finite M,N, unbounded | `proEtaleDerivedCategory Y (finiteCoefficientRing l E (n+1))`; no boundedness, perfectness, constructibility, or Tor assumption |
| Integral M,N and Hom constructible | `(constructibleIntegralHomPairs l E Y).FullSubcategory`; its entries belong to `sfIntegralConstructibleCategory`, and its property is precisely constructibility of the ambient `integralDerivedInternalHom` |
| Completed integral coefficient sheaf | `completedIntegralCoefficientSheafUnrestricted` / its commutative-ring refinement; `integralTowerModules` uses exactly that completed sheaf |
| Rational operations on integral objects | `rationalDerivedPullback`, `rationalDerivedTensor`, `rationalDerivedInternalHom`; their actual raw scalar-localization category is unchanged |
| Algebraically closed coefficients | Independent universe `v` for `(Ω : Type v)` with field, algebra and algebraic-closure instances; `commonStageDerived*` and the actual common-stage pair category |
| Canonical mu | The four recorded `canonical*PullbackTensor` families, and `pullbackTensorSystemComparison` on systems |
| Canonical c | `podFiniteHomComparison` is the actual finite transpose of mu inverse followed by pullback of evaluation; the other three comparisons use `podPartialHomComparison` and the uniquely normalized closed data |
| Natural isomorphism | The primary theorem gives actual natural isomorphisms of the four pair functors with those exact components. `podFiniteHomComparison_laws` and `PodPartialHomCompatibility` state invertibility and naturality for arbitrary arrows |
| Displayed evaluation equation, argument first | `podArgumentFirst_finite`, `podArgumentFirst_integral_rational`, and `podArgumentFirst_common`; `podArgumentFirstEvaluation` inserts the existing signed braiding, so these have exactly M tensor H as in the node |
| Every argument-first transpose | `podArgumentFirst_finite_transpose` and the transpose field of `PodArgumentFirstLaws`. The underlying Hom-first versions are also stated in the law declarations |
| Canonical shifts, both arguments | `podHomComplexShift_existsUnique` fixes degree k, p-th component as `(-1)^(a*k)` times the p+a component; `podDerivedHomShift_existsUnique` fixes the derived map by the actual K-injective augmentation. `podFiniteHomComparison_shift`, `podIntegralReindexedHom_shift`, and `podIntegralRationalHomComparison_shift` give the squares. `podCommonHomComparison_shift` gives their common-stage images at EVERY finite coefficient field. Rational/common shifts are expressed on their integral/finite-stage representatives; the already recorded localization/inclusion CommShift isomorphisms identify these with the chosen category shifts |
| Composition of scheme isomorphisms | `podFiniteHomComparison_comp`, `podIntegralHomComparison_comp`, `podRationalHomComparison_comp`, `podCommonHomComparison_comp`; the latter three use the published canonical `pullbackTensor*Composition` maps |
| Exact inverse-image equivalence at completed coefficients | `podCompletedRingMap` is a limit lift of `podCompletedRingProjection`; `podCompletedModuleInverseImage` uses sectionwise inverse image and the inverse of this actual ring map. Exactness instances and `podCompletedInverseImage_equivalence` record the equivalence |
| Canonical comparison with tower pullback | `podCompletedToTower` is inverse image of the actual reduction/completion unit, inverse total-limit reindexing, and inverse of the recorded tower model. `podCompletedToTower_laws` states naturality and invertibility on complete constructible inputs |
| All reduction projections | `podFiniteRestrictionOrdinary_existsUnique` fixes the local-section comparison by the adjunction unit; `podOrdinaryLimitReindexing_existsUnique` fixes all ordinary projections. `podLimitReindexing_existsUnique` imposes BOTH the actual resolution/unit square and every derived projection equation. Projection equations alone are never claimed to determine a derived map |
| Actual derived-system maps | `podSystemHomComparison` is `coefficientBaseChangeHom` on the sequence site itself, before evaluation. `podSystemHomComparison_laws` states isomorphism and `CoefficientEvaluationCompatible`, including actual system evaluation, transposition and internal composition |
| Prescribed finite fibers | `podSystemNormalized` and `podSystemHomComparison_fiber` identify the same system comparison through the dependency's `fiberHom` on normalized inputs; no claim is made that arbitrary systems have invertible fiber-Hom comparisons |
| Functorial total-limit realization | `PodLimitResolutionNormalization` fixes the actual right-derived-functor unit square. `podSystemHomComparison_realizedEvaluation` applies the specified `coefficientSequenceLimit` to the actual system evaluation equation |
| Integral/system compatibility before realization | `podReductionReindexingMap` is the actual adjunction mate of inverse image of the completion unit. `podHomReductionSquare` is an equality of maps in the derived category of systems, with beta and the prescribed comparisons. Applying total limit realizes this square; beta is not assumed invertible |
| Localized/common-stage maps and arbitrary localized Hom arrows | `podRationalClosed_existsUnique` fixes inverse transposition on every pure scalar tensor, as an ADDITIVE equivalence on the whole Hom group. `podRationalHomComparison_laws` identifies c itself with localization of integral c. `PodCommonTransposeNormalization` fixes inverse transposition on EVERY common-stage arrow representative, and `podCommonHomComparison_laws` is naturality in the actual Hom-colimit category. This fixes c as the common-stage image of the rational c through the specified tensor comparisons, without selecting arbitrary representatives |

Dependency declarations used:

- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteCoefficientRing`,
  `finiteDerivedPullback`, `finiteIntrinsicClosed`, `finiteIntrinsicTensorModels`,
  `finiteIntrinsicDerivedTensor`, `finiteIntrinsicDerivedInternalHom`,
  `finiteIntrinsicEvaluation`, `finiteIntrinsicTranspose`,
  `constructibleIntegralHomPairs`, `constructibleIntegralHom`,
  `constructibleIntegralPullback`, `constructibleIntegralTensor`,
  `constructibleRationalHomPairs`, `integralPairOfRationalHomPair`,
  `rationalDerivedPullback`, `rationalDerivedTensor`, `rationalDerivedInternalHom`,
  `commonStageHomPairs`, `commonStageDerivedPullback`, `commonStageDerivedTensor`,
  `commonStageDerivedInternalHom`, `commonStageHomObject`,
  `commonStageHomPairAtStage`, `commonStageHomComparison`, `commonStageTensorComparison`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`: `CoefficientClosedStructure`,
  `coefficientBaseChangeHom`, `CoefficientEvaluationCompatible`, the chosen
  `coefficientDerivedSystemEvaluationCalculus` with its `integralClosed`, `systemClosed`,
  `reduction`, `adjunction`, `reductionTensor`, `fiberHom` and normalization fields.
- `Sheaf.Paper.SemilinearDerivedSections` and its public dependencies provide the same
  derived sequence categories, geometric reindexing and specified limit realization;
  no private system evaluation or change-of-rings construction is introduced.
- `Sheaf.Paper.CompletedPullbackTensorComparison`: `pullbackTensorCalculus`,
  `pullbackTensorSequenceInverse`, `pullbackTensorSequenceDerived`,
  `pullbackTensorSystemComparison`, `pullbackTensorDerivedEvaluation`,
  `pullbackTensorSequenceInverseEvaluation`, `pullbackTensorLevelIntrinsic`,
  `pullbackTensorOrdinaryLimit`, `pullbackTensorLimitUnit`,
  `pullbackTensorIntegralPullbackModel`, `pullbackTensorIntegralTensorModel`, and the
  four actual canonical tensor comparisons.
- `Sheaf.Paper.DerivedPullbackTensorIso`: the existing integral/rational/common braidings
  and composition comparisons. Its source and complete signatures were read. An initially
  redundant integral composition construction was removed in favor of this declaration;
  the remaining theorem only identifies its completion-unit normalization.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `isoSectionwiseInverseImage`, `isoSectionwiseConstantMap`,
  `isoSectionwiseModuleInverseImage` and its additive/limit/colimit instances;
  `proEtaleIsoPostcompose` comes from its published dependency.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`: `coefficientHomComponent`,
  `coefficientHomResolution`, `coefficientHomResolutionIso`, the fixed augmentation
  supplied by the published K-injective resolution API.
- Mathlib: `Scheme.ProEt`, `Scheme.ProEt.topology`, `IsIso`, `DerivedCategory.Q`,
  the standard cochain/derived shifts, `ObjectProperty` full subcategories, `limit.lift`,
  actual limit projections, `MorphismProperty.Over.mapPullbackAdj`.
- The exact derived API gives `Functor.mapDerivedCategoryNatIso`,
  `Functor.mapDerivedCategoryCompIso`, `mapDerivedCategoryFactors`, and standard CommShift.
  `sfIntrinsicPullbackComp` is the intrinsic finite coefficient composition comparison.
- `Padic.finite_coefficientExtensionRing` and `Padic.coefficientExtensionRing` supply
  the dependency's actual finite quotients. The scheme-morphism-properties dependency
  is the existing `IsIso` convention and needs no replacement declaration.

All stated proof dependencies have their recorded modules imported without `public`
unless already a direct public statement dependency. The complete sixteen-step node
proof, with its dependency ids, is included in the primary theorem docstring.

Edge cases checked before and during statement construction:

- Zero objects and empty schemes require no nonempty site or support hypothesis.
- Exponent one is the index zero case; no positive exponent is silently dropped.
- Finite M,N remain arbitrary and unbounded, including nonperfect complexes.
- Integral completeness is used only on the constructible domain to invert the canonical
  unit; no claim is made that the unit is invertible on every ambient object.
- Both inputs of integral Hom retain exactly the stated Hom-constructibility qualification.
- Negative and zero shifts are included. The normalization records all integer signs, not
  just existence of a shift isomorphism.
- All finite coefficient extensions, including ramified ones and ell=2, use the recorded
  rings and scalar comparisons; no etaleness or perfectness is added.
- Natural transformations at field stages range over every arrow of the actual localized
  or common-stage category, rather than integral arrows alone.
- Site object and morphism universes remain distinct. The closure universe is independent.
- A derived-limit comparison normalized only by finite projections would be insufficient;
  the actual resolution/unit normalization is explicitly present.

Searches for an existing statement (2026-10-18):

1. `msearch.py ... leanfinder`: “Pullback by a scheme isomorphism preserves derived internal
   Hom, evaluation, transposition, shifts and completed coefficient systems”. Eight hits,
   all ordinary `Scheme.Modules` pullback comparisons; none is this statement.
2. `msearch.py ... loogle`: `CategoryTheory.MonoidalClosed.ofEquiv`. Three hits on ordinary
   transport of closed structure; none identifies the recorded derived operations or
   completed reduction-system maps.
3. `msearch.py ... leansearch`: “exact equivalence of ringed sites derived internal Hom
   evaluation adic completed coefficients”. Eight unrelated adic-completion hits.
4. `msearch.py ... grep`: `internalHom.*[Ii]so|[Ii]so.*internalHom|[Ee]valuation.*[Ee]quivalence`
   under `CategoryTheory/Monoidal`: no exact match.
5. `rg` in Mathlib, upstream `WeilConjectures/` and side `lean/Sheaf/` for automorphism,
   Hom evaluation, shifts and the new declaration names. `StrictWeilDualTate` concerns the
   small etale coefficient category, and upstream `ProEtale/Adic/HomCoherence` concerns
   underived algebraically closed coefficient sheaves; their signatures were read and do
   not give this unbounded, completed, system-normalized statement. `grep -rn` of this
   node id in upstream gives no match. No new declaration name collides.
6. Targeted side-source search found `DerivedPullbackTensorIso` and reused its braidings
   and composition maps. The existing `derivedInternalHom_shift_comparison` has a
   same-universe small-site interface; the statement here retains the actual independent
   pro-etale universes and fixes the signed map uniquely via existing mixed-universe
   Hom-product projections and resolution factors. No second Hom or tensor is defined.

No statement dispute or source-based correction is needed.

## Second reading by Q66

The dispatcher explicitly assigns independent review to the maintainer and forbids starting
other agents. This section is Q66's second pass with the node and module open; it does not
claim an independent worker read.

The table above was checked against every sentence of the node. The second pass found and
repaired these points: argument-first evaluation/transposition is now written explicitly
using the published signed braidings; shift equations retain both arguments and negative
integers; constructible inclusion shift isomorphisms are inserted instead of identifying
chosen subcategory shift objects definitionally; completed inverse image is compared to
tower pullback using the actual unit; a resolution-unit square was added because derived
projections alone do not determine a map; field composition uses the already recorded
comparisons instead of a duplicate definition; system evaluation is established on the
actual derived system category, with its finite fibers and functorial realization stated
separately. Field shift squares are expressed on the integral/common finite representatives,
consistent with the node's field-stage image convention. No hypothesis on perfectness,
boundedness of finite inputs, flatness of g, or equality of site universes was introduced.

The main theorem records the four natural isomorphisms; all the clause-specific companion
statements and their canonical construction helpers are included in `lean.declarations`.
