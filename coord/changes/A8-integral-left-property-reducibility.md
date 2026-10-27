# integralTensorLeftProperty

## Reason

Keep the canonical completed tensor and quotient functors abstract while proving
normalization. The old predicate is factored through
`integralTensorLeftModelProperty`, with the coefficient category, good-complex property, tower, finite formula,
quotient, output shift, shift comparison, tensor and model comparison as parameters. The canonical predicate
is its abbreviation. Expanding that abbreviation and the generic definition
recovers the old body definitionally; no hypothesis or conclusion changes.
The exact original formula and the canonical specialization passed an `Iff.rfl`
check against the patched dependency. All three current direct consumers compiled unchanged against the patched dependency.
The module is unclaimed.

## Old

```lean
def integralTensorLeftProperty (W : Scheme.{u}) (r : ℤ)
    (σ : tensorShiftFirst (Integral l E W) r ⋙ integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙ shiftFunctor (Integral l E W) r) : Prop :=
  ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
    ∃ (hP : integralOperationsGoodComplex l E W (P.obj⟦r⟧))
      (α : (integralOperationsTensorTowerFunctor l E W).obj (P.obj⟦r⟧, Q.obj) ≅
        (integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj) ⋙
          shiftFunctor (CochainComplex (integralTowerModules l E W) ℤ) r),
      integralTensorLeftFormula l E W P.obj Q.obj r α ∧
      ∃ (δ : CochainComplex.mappingCone (completedTensorShiftOneSub
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj⟦r⟧, Q.obj))) ≅
          (CochainComplex.mappingCone (completedTensorShiftOneSub
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))))⟦r⟧),
        completedTensorShiftConeFormula
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
            ((integralOperationsTensorTowerFunctor l E W).obj (P.obj⟦r⟧, Q.obj)) r α δ ∧
        (integralCompletedTensor l E W).map
            (((DerivedCategory.Q.commShiftIso r).hom.app P.obj),
              𝟙 (DerivedCategory.Q.obj Q.obj)) ≫
          σ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (shiftFunctor (Integral l E W) r).map
            ((integralCompletedTensorComparison l E W).hom.app (P, Q)) =
        (integralCompletedTensorComparison l E W).hom.app (⟨P.obj⟦r⟧, hP⟩, Q) ≫
          DerivedCategory.Q.map
            (completedTensorShiftRoosIso
              ((integralOperationsTensorTowerFunctor l E W).obj (P.obj, Q.obj))
              ((integralOperationsTensorTowerFunctor l E W).obj (P.obj⟦r⟧, Q.obj)) r δ).hom ≫
          (DerivedCategory.Q.commShiftIso r).hom.app
            ((integralOperationsTensorComplexFunctor l E W).obj (P.obj, Q.obj))
```

## New

```lean
abbrev integralTensorLeftProperty (W : Scheme.{u}) (r : ℤ)
    (σ : tensorShiftFirst (Integral l E W) r ⋙ integralCompletedTensor l E W ≅
      integralCompletedTensor l E W ⋙ shiftFunctor (Integral l E W) r) : Prop :=
  integralTensorLeftModelProperty r (integralOperationsGoodComplex l E W)
    (integralOperationsTensorTowerFunctor l E W)
    (fun P Q ↦ integralTensorLeftFormula l E W P Q r) DerivedCategory.Q
    (shiftFunctor (Integral l E W) r) (DerivedCategory.Q.commShiftIso r)
    (integralCompletedTensor l E W) (integralCompletedTensorComparison l E W) σ
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralTensorShiftProperties | unclaimed | Definitionally identical predicate; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | H7 | Definitionally identical predicate; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorLeftShiftUnique | A8 | Definitionally identical predicate; no adaptation. |
| Sheaf.SixFunctors.CompletedTensorShiftAddOnGood | unclaimed | Definitionally identical predicate; no adaptation. |

These include the current users rechecked on 2026-10-26 with `tools/downstream.py --uses`
and the assigned module's new proof uses. No consumer signature or body changes.
Targets using this definition have exactly the same meaning: both the old and
new predicates require the identical generator or good-model normalization.
The independent definition review can check the verbatim bodies above.
The factored definition compiled, and a separate mirrored check proved its
exact equality with the old predicate by `Iff.rfl`. The three current direct
consumers compiled unchanged against the patched dependency:
`IntegralOperationShiftData`, `SystemTensorLeftShiftUnique`, and
`SystemTensorShiftRepresentativeModels`. The two quarantined consumers are preserved
without adaptation; this check does not restore them.

This definition change reopens meaning review for affected targets under
AGENTS.md §4; the verbatim types and bodies are the evidence for that review.

## Status

landed 20261026T022806-L-446879 2026-10-26 (merge of deliver/A8/Sheaf.SixFunctors.IntegralTensorLeftShiftUnique)
