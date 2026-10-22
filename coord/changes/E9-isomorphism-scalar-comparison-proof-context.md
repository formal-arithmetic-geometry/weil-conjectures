# WeilConjectures.isomorphismComparison_scalarExtension

## Reason

The stage-3 preflight requires a change record for additional proof-context commands
in `Sheaf.Paper.IsomorphismComparisonScalarExtension`. The delivery fills all five
original theorem proofs using proved private helpers. No existing public theorem
signature, existing definition body, declaration visibility or public import changes.
No new public declaration or exported instance is introduced.

The extra commands control elaboration or provide lexical names and notation for
these proofs. Their exact scopes are recorded below. All definitions used by targets
retain their original bodies, so no target meaning changes and no statement review
is reopened. No consumer needs adaptation.

## Old

The original file-wide command block was:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
```

There were no named `DerivedComparison`, `TensorComparison` or `ComparisonSquare`
sections, no additional universe names, and no additional local proof attributes.
For reference, the original main declaration was exactly:

```lean
theorem isomorphismComparison_scalarExtension
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    (integralScalarExtension l E L ι X).map
        (inverseImagePullbackComparisonDerived l E g hX hY K) ≫
      isomorphismComparisonScalarAlpha l E L ι g hX hY K hK =
    isomorphismComparisonScalarBeta l E L ι g hX hY K hK ≫
      inverseImagePullbackComparisonDerived l L g hX hY
        ((integralScalarExtension l E L ι Y).obj K) := by
  sorry
```

All five original theorem headers are retained verbatim in the delivered file.
The existing definitions `isomorphismScalarSheafModel`, `isomorphismScalarTensor`,
`isomorphismScalarTensorDerived`, `isomorphismComparisonScalarAlpha` and
`isomorphismComparisonScalarBeta` retain their bodies verbatim.

## New

The additional lexical/elaboration commands are:

```lean
set_option backward.isDefEq.respectTransparency.types true
open scoped ChangeOfRings
```

The stricter type-transparency setting applies throughout this file.

The initial ordinary tensor-model application also supplies its coefficient maps
and both functors explicitly, avoiding unnecessary inference.

These commands affect elaboration of this file; neither exports an option or opens a scope in
importing files. The existing file-wide instance removal and other options above
are unchanged.

The following local attributes occur inside `section DerivedComparison`, which
ends immediately after `isomorphismScalarModel_existsUnique`:

```lean
attribute [local irreducible] integralScalarReductionWitness integralScalarReduction
  integralScalarTensorSection
attribute [local irreducible] completedScalarChangeData
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
```

These attributes keep large chosen constructions folded during proof elaboration. Their
bodies and global reducibility attributes are unchanged.

Inside `section TensorComparison`, closed before `isomorphismScalarTensor`, the
proofs use:

```lean
open AlgebraicGeometry
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
attribute [local irreducible] integralCompletedScalarMap inverseImageCompletedCoefficientMap
universe v
```

The repeated variable block supplies the same coefficient parameters, with no
additional public binder. The universe `v` occurs only in the private generic
presheaf/adjunction proof. The local irreducibility attributes are closed with the
section.

Inside `section ComparisonSquare`, closed before the original main theorem, the
private generic Roos and localization helpers use:

```lean
universe r s
open AlgebraicGeometry
```

The additional instance-removal commands are declaration-scoped wrappers, with
these exact payloads, applied only to the following proved declaration:

```lean
attribute [-instance] SheafOfModules.instPreadditive in
attribute [-instance] integralOperationsAbSheafify
  integralOperationsAbLocallyBijective integralOperationsSiteSmall in
```

The first is used for the derived-model proof and the good-representative helper; the
second is used for the sheaf tensor and square helpers and tensor-model proof.
When both occur they are nested around that one declaration. They prevent
ambiguous or looping instance search at independent coefficient universes. No
instance is globally removed by these wrappers.

Every new helper is a proved private theorem. All original public definitions
and statement signatures, including universes and hypotheses, are preserved.
The main theorem now has the complete proof:

```lean
theorem isomorphismComparison_scalarExtension
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y))
    (hK : sfIntegralConstructible l E Y K) :
    (integralScalarExtension l E L ι X).map
        (inverseImagePullbackComparisonDerived l E g hX hY K) ≫
      isomorphismComparisonScalarAlpha l E L ι g hX hY K hK =
    isomorphismComparisonScalarBeta l E L ι g hX hY K hK ≫
      inverseImagePullbackComparisonDerived l L g hX hY
        ((integralScalarExtension l E L ι Y).obj K) := by
  exact scalarCompletedSquare l E L ι g hX hY
    (scalarDerivedSquare l E L ι g hX hY (scalarRoosSquare l E L ι g)) K hK
```

## Users

`python3 tools/downstream.py Sheaf.Paper.IsomorphismComparisonScalarExtension
--uses <each of the ten original public declaration names>` listed the following
66 downstream modules. The claims shown are the current coordination records.
A whole-word use scan finds direct external uses only in
`Sheaf.Paper.PointAutomorphismTransportScalarExtension`: its constructibility
projections and `pointTransportBetaIso` use the unchanged
`isomorphismComparisonInputs_constructible` and `isomorphismScalarTensorDerived`.
Those definitions and their endpoints remain exactly as before. The other rows
are transitive importers. No consumer statement becomes stronger, weaker or
different, and no consumer file is adapted in this delivery. The maintainer's
global build verifies the complete library after landing.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | E9 | Five proofs completed; interface preserved. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.FourierArtinSchreierProperties | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.PointAutomorphismTransportScalarExtension | unclaimed | Direct uses retain the same definitions and statements. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.RealWeights | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Transitive consumer; interface preserved. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Transitive consumer; interface preserved. |

## Status

landed 20261022T011830-L-3220631 2026-10-22 (merge of deliver/E9/Sheaf.Paper.IsomorphismComparisonScalarExtension)
