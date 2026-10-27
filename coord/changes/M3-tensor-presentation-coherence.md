# WeilConjectures.ScalarExtensionTower tensor normalization and realizationModels

## Reason

The tensor normalization has the same finite-presentation defect already repaired for
pullback (S9) and scalar (J5): finite derived evaluations are conservative, not faithful
on arbitrary morphisms. Twisting eC by an automorphism invisible after each finite derived
evaluation keeps the old hypotheses and the generator-normalized strict q, but changes
the required total-limit equation. Require the existing whole-system adjunction-transpose
coherence for each input presentation. This does not change the completed tensor, scalar
extension, finite coefficients, generator formula, comparison equation or input objects.
Canonical coherent presentations exist for every good input by
coherentPrimitiveReductionPresentation. The T6 mathematical counterexample, also reviewed
in J5-scalar-presentation-coherence.md, tests the tensor clause by taking the other factor
to be the coefficient unit. This is not claimed as a Lean-certified refutation.

The source node assumes l invertible on both schemes. realizationModels omitted it even
though the existing scalar-model existence theorem requires it. Restore that hypothesis
only to this auxiliary theorem; its sole caller already has both residue-field
invertibility instances. Its public theorem signature remains identical. The main
scalarExtensionTowerCoherence and Challenge signatures remain identical. The old false
normalization is corrected, not proved by this delivery.

The tensor realization is an explicit construction: start with the uniquely
strict-Roos-normalized pullbackTensorIntegralTensorModel, then use the unit-compatible
comparison of reduction left adjoints and the canonical tensor-Hom-compatible comparison
of closed tensors. No arbitrary witness of a mere existence theorem is selected as new
data. Only normalization of this fixed constructed realization remains a new named hole.
The scalar half uses the existing primitiveQuotientScalarModelExistence theorem.

Edge checks: both zero inputs and the coefficient unit, empty schemes, the first positive
quotient, identity coefficient extension, and ramified scalar extension all retain the
same construction. No quotient-ring flatness assumption is added. The new coherence
conditions exclude invisible presentation twists, while the original canonical
presentations satisfy them. Any target-meaning review depending on this auxiliary
normalization interface should be reopened; coefficient data and target statements
are unchanged.

## Old

```lean
def IsTensorModelNormalized (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W)
    (realization : integralCompletedTensor.{u, u} l E W ≅ S.reduction.prod S.reduction ⋙
      S.systemClosed.tensor ⋙ coefficientSequenceLimit.{u, u} l E W) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory)
    (C D : Complex l E W)
    (eC : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (eD : S.reduction.obj (DerivedCategory.Q.obj Q.obj) ≅ DerivedCategory.Q.obj D)
    (κC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj P.obj)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj Q.obj)
    (hC : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) C)
    (hD : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) D),
    CoefficientReductionPresentation.{u, u} l E W S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C eC κC →
    CoefficientReductionPresentation.{u, u} l E W S.toCoefficientDerivedSystemReduction
      Q.obj Q.property.1 D eD κD →
    ∃ q : (((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l E W).obj (C, D))).asFunctor ≅
      (integralOperationsTensorTowerFunctor.{u, u} l E W).obj (P.obj, Q.obj),
      (∀ (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
        (x : (C.X p).val.obj (op (n, U.unop)))
        (y : (D.X r).val.obj (op (n, U.unop))),
        ((q.hom.app (op n)).f (p + r)).val.app U
          (integralComparisonRestrictedSection.{u, u} l E W
            (((tensor l E W).obj (C, D)).X (p + r)) n U
            (generator l E W C D p r (op (n, U.unop)) x y)) =
          integralTensorGenerator l E W P.obj Q.obj n p r U
            (((κC n).hom.f p).val.app U (coefficientEvaluationSection.{u, u} l E W (C.X p) n U x))
            (((κD n).hom.f r).val.app U
              (coefficientEvaluationSection.{u, u} l E W (D.X r) n U y))) ∧
      FiveStepEquation
        (realization.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
        ((coefficientSequenceLimit.{u, u} l E W).map
          (S.systemClosed.tensor.map (Prod.mkHom eC.hom eD.hom)))
        ((coefficientSequenceLimit.{u, u} l E W).map
          ((S.systemTensorModel.iso _ _ _ C D hC hD).inv))
        ((integralComparisonRoosBridge.{u, u} l E W ρ
          ((tensor l E W).obj (C, D))).hom)
        (DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom))
        ((integralCompletedTensorComparison.{u, u} l E W).hom.app (P, Q))

theorem realizationModels (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W) (ML : CompletedOperations.Models.{u, u} l L W) :
    ∀ a : Bool, Nonempty (TensorModel l E (W a) (ME.calculus a) (ME.roos a)) ∧
      Nonempty (IntegralComparisonScalarModel.{u, u} l E L ι (W a)
        (ME.calculus a) (ML.roos a))
```

The new tensorModelRealization declaration did not previously exist.

## New

```lean
def IsTensorModelNormalized (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l E W)
    (realization : integralCompletedTensor.{u, u} l E W ≅ S.reduction.prod S.reduction ⋙
      S.systemClosed.tensor ⋙ coefficientSequenceLimit.{u, u} l E W) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory)
    (C D : Complex l E W)
    (eC : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (eD : S.reduction.obj (DerivedCategory.Q.obj Q.obj) ≅ DerivedCategory.Q.obj D)
    (κC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj P.obj)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E W n).obj Q.obj)
    (hC : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) C)
    (hD : CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf.{u, u} l E W) D),
    CoefficientReductionPresentation.{u, u} l E W S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C eC κC →
    CoefficientReductionPresentation.{u, u} l E W S.toCoefficientDerivedSystemReduction
      Q.obj Q.property.1 D eD κD →
    IsIntegralComparisonPresentationCoherent l E W S P.obj C eC κC →
    IsIntegralComparisonPresentationCoherent l E W S Q.obj D eD κD →
    ∃ q : (((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex (.up ℤ)).obj
        ((tensor l E W).obj (C, D))).asFunctor ≅
      (integralOperationsTensorTowerFunctor.{u, u} l E W).obj (P.obj, Q.obj),
      (∀ (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
        (x : (C.X p).val.obj (op (n, U.unop)))
        (y : (D.X r).val.obj (op (n, U.unop))),
        ((q.hom.app (op n)).f (p + r)).val.app U
          (integralComparisonRestrictedSection.{u, u} l E W
            (((tensor l E W).obj (C, D)).X (p + r)) n U
            (generator l E W C D p r (op (n, U.unop)) x y)) =
          integralTensorGenerator l E W P.obj Q.obj n p r U
            (((κC n).hom.f p).val.app U (coefficientEvaluationSection.{u, u} l E W (C.X p) n U x))
            (((κD n).hom.f r).val.app U
              (coefficientEvaluationSection.{u, u} l E W (D.X r) n U y))) ∧
      FiveStepEquation
        (realization.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
        ((coefficientSequenceLimit.{u, u} l E W).map
          (S.systemClosed.tensor.map (Prod.mkHom eC.hom eD.hom)))
        ((coefficientSequenceLimit.{u, u} l E W).map
          ((S.systemTensorModel.iso _ _ _ C D hC hD).inv))
        ((integralComparisonRoosBridge.{u, u} l E W ρ
          ((tensor l E W).obj (C, D))).hom)
        (DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom))
        ((integralCompletedTensorComparison.{u, u} l E W).hom.app (P, Q))

theorem realizationModels (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W) (ML : CompletedOperations.Models.{u, u} l L W)
    (hl : ∀ (a : Bool) (x : W a), IsUnit (l : (W a).residueField x)) :
    ∀ a : Bool, Nonempty (TensorModel l E (W a) (ME.calculus a) (ME.roos a)) ∧
      Nonempty (IntegralComparisonScalarModel.{u, u} l E L ι (W a)
        (ME.calculus a) (ML.roos a))

def tensorModelRealization (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W) :
    integralCompletedTensor.{u, u} l E W ≅ S.reduction.prod S.reduction ⋙
      S.systemClosed.tensor ⋙ coefficientSequenceLimit.{u, u} l E W := by
  let T := pullbackTensorCalculus l E W
  let a := T.adjunction.leftAdjointUniq S.adjunction
  exact pullbackTensorIntegralTensorModel l E W ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (NatIso.prod a a) T.systemClosed.tensor ≪≫
        Functor.isoWhiskerLeft (S.reduction.prod S.reduction)
          (CoefficientClosedStructure.comparison T.systemClosed S.systemClosed))
      (coefficientSequenceLimit l E W)
```

TensorModel.normalization retains its declared predicate type; the predicate body now
has the two coherence premises. The new theorem tensorModelRealization_normalized is
recorded at stage3-pur-scalar-tensor-model-normalization and has its full source and
proof in words in the new module.

## Users

The whole-word last-component scan of tools/downstream.py --uses
IsTensorModelNormalized TensorModel, and the realizationModels scan, give the rows below.
The ten homonymous TensorModel users are included to document the over-approximation.
The two changed existing dependency modules were unclaimed on the server when checked;
no source-library module is edited.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.CompactSupportCompletedProjectionData` | unclaimed in shared snapshot | Homonymous TensorModel in another namespace; no use of the changed predicate. No edit. |
| `Sheaf.Paper.CompactSupportScalarProjectionIdentification` | unclaimed in shared snapshot | Homonymous TensorModel in another namespace; no use of the changed predicate. No edit. |
| `Sheaf.Paper.CompletedComparisonQuotientRealizationDefs` | unclaimed in shared snapshot | Direct importer; no use of realizationModels or the changed normalization projection. No edit. |
| `Sheaf.Paper.ConcreteIntegralProjectionCone` | unclaimed in shared snapshot | Homonymous TensorModel in another namespace; no use of the changed predicate. No edit. |
| `Sheaf.Paper.FrobeniusEvaluationProjectionCoherence` | unclaimed in shared snapshot | Homonymous TensorModel in another namespace; no use of the changed predicate. No edit. |
| `Sheaf.Paper.IntegralComparisonSystemData` | unclaimed in shared snapshot | Direct importer; no use of realizationModels or the changed normalization projection. No edit. |
| `Sheaf.Paper.IntegralProjectionOperationPresentation` | unclaimed in shared snapshot | Homonymous TensorModel in another namespace; no use of the changed predicate. No edit. |
| `Sheaf.Paper.IntegralProperOperationProjection` | unclaimed in shared snapshot | Homonymous TensorModel in another namespace; no use of the changed predicate. No edit. |
| `Sheaf.Paper.IntegralScalarPullbackCounitCompatibility` | unclaimed (server checked) | Sole realizationModels caller: pass its existing residue-field units at the two calls. Public signature and imports unchanged. |
| `Sheaf.Paper.LisseTensorNormalization` | unclaimed in shared snapshot | Homonymous TensorModel in another namespace; no use of the changed predicate. No edit. |
| `Sheaf.Paper.LisseTensorPullbackRealizationData` | unclaimed in shared snapshot | Homonymous TensorModel in another namespace; no use of the changed predicate. No edit. |
| `Sheaf.Paper.RationalRealizationTensorComparison` | F9 | Direct importer; no use of realizationModels or the changed normalization projection. No edit. |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | M3 | Construct both models; realizationModels receives the source invertibility hypothesis. |
| `Sheaf.Paper.ScalarExtensionTowerRealizationData` | unclaimed (server checked) | Predicate-body repair; existing signatures and public imports unchanged. |
| `Sheaf.Paper.ScalarTowerPullbackLimitSquare` | unclaimed in shared snapshot | Supplied-model conditional equation unchanged; never applies or constructs the normalization field. No edit. |
| `Sheaf.Paper.ScalarTowerTensorLimitSquare` | unclaimed in shared snapshot | Supplied-model conditional equation unchanged; never applies or constructs the normalization field. No edit. |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed in shared snapshot | Homonymous TensorModel in another namespace; no use of the changed predicate. No edit. |
| `Sheaf.SixFunctors.ProductNormalizationRealizationTransport` | unclaimed in shared snapshot | Homonymous TensorModel in another namespace; no use of the changed predicate. No edit. |

The sole caller adaptation changes only the two applications at original lines 128--130:
insert the source unit proof, by Bool cases and isUnit_of_invertible. Every theorem and
definition signature in the caller stays identical. All existing public imports stay.
The independent review and delivery importer check verify the current originals against
the changed files, in addition to the explicit single-file importer checks.

The node correction uses the existing validator's required author suffix "stage 2";
this packet is a stage-3 auxiliary-definition repair, as recorded in its what field.

## Status

landed 20261027T210136-L-1662686 2026-10-27 (merge of deliver/M3/Sheaf.Paper.ScalarExtensionTowerCoherence)
