# WeilConjectures.CompletedOperations.Models and tensorRealization

## Reason

The source specifies derived tensor presentations by their normalized tensor–Hom adjunctions. It does not identify independently chosen monoidal structures by propositional equality. The former system_closed and integral_closed fields demanded that extra strictification; no available canonical-model theorem supplies it. Use the unique adjunction-compatible comparison instead. The comparison is constructed from the adjunctions, is natural in both arguments, and preserves evaluation and every transpose. comparison_eqToIso proves that on equal presentations it is exactly the former equality cast. Thus this is a repair of presentation data, preserving the specified tensor and quotient maps up to their canonical identification. No target signature is edited. Because this definition occurs below targets, its meaning is reopened for independent review.

## Old

```lean
structure Models {S : Type s} (W : S → Scheme.{t}) where
  /-- The recorded reduction/total-limit adjunction. -/
  calculus : ∀ a : S, CoefficientDerivedSystemCalculus l E (W a)
  /-- Canonical total tensor, action unit and signed interchange on whole systems. -/
  system : ∀ a : S, RingedSiteDualityModel.{t + 1, t, u, (max u (t + 1)) + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
    (coefficientSequenceCommRingSheaf l E (W a))
  /-- These are presentations of the same system closed tensor. -/
  system_closed : ∀ a : S, (system a).closed = (calculus a).systemClosed
  /-- The integral tensor is the recorded ordinary tensor used by completion. -/
  integral_closed : ∀ a : S,
    (calculus a).integralClosed = (IntegralOnSlice.duality l E (W a) none).closed
  /-- Completion as the reduction/total-limit composite. -/
  completion : ∀ a : S, IntegralOnSlice.completion l E (W a) none ≅
    (calculus a).reduction ⋙ coefficientSequenceLimit l E (W a)
  /-- Unit normalization determines this comparison, including its maps. -/
  completion_unit : ∀ (a : S) (K : DerivedCategory (scalarReductionSource l E (W a))),
    (IntegralOnSlice.completionUnit l E (W a) none).app K ≫
        (completion a).hom.app K = (calculus a).adjunction.unit.app K
  /-- The actual total-limit/Roos comparison with its K-injective normalization. -/
  roos : ∀ a : S, IntegralComparisonRoosModel l E (W a)
  /-- Pullback is normalized on all K-flat quotient presentations. -/
  pullback : ∀ {a b : S} (f : W a ⟶ W b),
    IntegralComparisonPullbackModel l E f (calculus b) (roos a)


def tensorRealization (a : S) : IntegralOnSlice.completedTensor l E (W a) none ≅
    ((M.calculus a).reduction.prod (M.calculus a).reduction) ⋙
      tensor l E M a ⋙ coefficientSequenceLimit l E (W a) :=
  isoWhiskerLeft (IntegralOnSlice.duality l E (W a) none).closed.tensor (M.completion a) ≪≫
    isoWhiskerRight
      (isoWhiskerRight
        (eqToIso (congrArg CoefficientClosedStructure.tensor (M.integral_closed a).symm))
          (M.calculus a).reduction ≪≫
        (M.calculus a).reductionTensor ≪≫
        isoWhiskerLeft ((M.calculus a).reduction.prod (M.calculus a).reduction)
          (eqToIso (congrArg CoefficientClosedStructure.tensor (M.system_closed a).symm)))
      (coefficientSequenceLimit l E (W a))
```

## New

```lean
structure Models {S : Type s} (W : S → Scheme.{t}) where
  /-- The recorded reduction/total-limit adjunction. -/
  calculus : ∀ a : S, CoefficientDerivedSystemCalculus l E (W a)
  /-- Canonical total tensor, action unit and signed interchange on whole systems. -/
  system : ∀ a : S, RingedSiteDualityModel.{t + 1, t, u, (max u (t + 1)) + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
    (coefficientSequenceCommRingSheaf l E (W a))
  /-- Completion as the reduction/total-limit composite. -/
  completion : ∀ a : S, IntegralOnSlice.completion l E (W a) none ≅
    (calculus a).reduction ⋙ coefficientSequenceLimit l E (W a)
  /-- Unit normalization determines this comparison, including its maps. -/
  completion_unit : ∀ (a : S) (K : DerivedCategory (scalarReductionSource l E (W a))),
    (IntegralOnSlice.completionUnit l E (W a) none).app K ≫
        (completion a).hom.app K = (calculus a).adjunction.unit.app K
  /-- The actual total-limit/Roos comparison with its K-injective normalization. -/
  roos : ∀ a : S, IntegralComparisonRoosModel l E (W a)
  /-- Pullback is normalized on all K-flat quotient presentations. -/
  pullback : ∀ {a b : S} (f : W a ⟶ W b),
    IntegralComparisonPullbackModel l E f (calculus b) (roos a)


def tensorRealization (a : S) : IntegralOnSlice.completedTensor l E (W a) none ≅
    ((M.calculus a).reduction.prod (M.calculus a).reduction) ⋙
      tensor l E M a ⋙ coefficientSequenceLimit l E (W a) :=
  isoWhiskerLeft (IntegralOnSlice.duality l E (W a) none).closed.tensor (M.completion a) ≪≫
    isoWhiskerRight
      (isoWhiskerRight
        (CoefficientClosedStructure.comparison
          (IntegralOnSlice.duality l E (W a) none).closed (M.calculus a).integralClosed)
          (M.calculus a).reduction ≪≫
        (M.calculus a).reductionTensor ≪≫
        isoWhiskerLeft ((M.calculus a).reduction.prod (M.calculus a).reduction)
          (CoefficientClosedStructure.comparison (M.calculus a).systemClosed (M.system a).closed))
      (coefficientSequenceLimit l E (W a))
```

## Users

The tools/downstream.py --uses scan finds the following whole-word matches (including homonyms). No consumer uses either removed field. The tensorRealization users use its type and naturality, with no unfolding of the equality casts.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.CoefficientDualModelTransport` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.CompactSupportScalarCoordinates` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.CompletedCoefficientFamilyTransportModels` | unclaimed | Uses completed-operation model projections and canonical comparison types; none uses removed fields. Mathematical operation and naturality statements are preserved under the canonical identification. |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | unclaimed | Uses completed-operation model projections and canonical comparison types; none uses removed fields. Mathematical operation and naturality statements are preserved under the canonical identification. |
| `Sheaf.Paper.ConcreteProjectionReductionSquare` | D7 | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.ConstructibleMateCoherence` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.ConstructibleWeilModelSquares` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.FdPullbackAugmentationCounitMatching` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.FrobeniusEvaluationProjectionCoherence` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.IntegralCoherenceTower` | B5 | Uses completed-operation model projections and canonical comparison types; none uses removed fields. Mathematical operation and naturality statements are preserved under the canonical identification. |
| `Sheaf.Paper.IntegralTowerLimitComparison` | unclaimed | Uses completed-operation model projections and canonical comparison types; none uses removed fields. Mathematical operation and naturality statements are preserved under the canonical identification. |
| `Sheaf.Paper.NormalizedCompletedOperationModels` | B2 | Repaired module; constructs the same primitive data with canonical tensor comparisons. |
| `Sheaf.Paper.PfReductionProperOpenIdentities` | A9 | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.PodCompletionReindexSubstitution` | unclaimed | Uses completed-operation model projections and canonical comparison types; none uses removed fields. Mathematical operation and naturality statements are preserved under the canonical identification. |
| `Sheaf.Paper.PodCounitScalarWordCoordinates` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.PointSystemRoosTransport` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.QcqsIntegralScalarExtensionCTF` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | X7 | Uses completed-operation model projections and canonical comparison types; none uses removed fields. Mathematical operation and naturality statements are preserved under the canonical identification. |
| `Sheaf.Paper.SemilinearExchangeCubeCoherence` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.SmoothPurityReductionDerivedMonoidalTower` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.SystemScalarProjectionIdentification` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.Paper.WeilChosenDualityExchange` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |
| `Sheaf.SixFunctors.OpenScalarTensorNormalization` | unclaimed | Homonymous Models in another namespace; no use of the changed structure. |

No consumer adaptations are necessary. In particular PodCompletionReindexSubstitution pins its tensor model via HEq; the canonical adjunction comparison preserves the same derived tensor realization rather than introducing an arbitrary isomorphism. Its statement remains the same normalized-representative requirement.

## Status

landed 20261025T211939-L-4169961 2026-10-25 (merge of deliver/B2/Sheaf.Paper.NormalizedCompletedOperationModels)
