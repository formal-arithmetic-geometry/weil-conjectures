# AlgebraicGeometry.exists_exactSource_evaluation_local_comparisons

## Reason

The original statement and every universe, binder and visibility stay identical.
Comparing the over-site derived equivalence with the standard open-scheme localization
exceeds the default 200000 elaboration heartbeats. The theorem compiles within the
single-file wall-clock limit when its declaration-local budget is 1000000.
A proof-local option alone does not increase the surrounding declaration's budget.
The static interface checker conservatively records a changed command, so this record
makes the exact setting and its lack of a semantic effect reviewable.

## Old

The declaration uses the default 200000 heartbeat budget. Its signature is:

```lean
theorem exists_exactSource_evaluation_local_comparisons (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (_hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (_hdual : (localEvaluationDual X U P).IsKFlat)
    (_eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)
    (_eN : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj N ≅ DerivedCategory.Q.obj F)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (_hf : IsLocalOrdinaryEvaluation X U P F f) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ a : R.obj (N ⊗ D) ≅ DerivedCategory.Q.obj (localEvaluationTensor X U P F),
      ∃ b : R.obj (H.obj (op K, N)) ≅
          DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F),
        R.map g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f
```

## New

The identical signature is preceded by the declaration-local command:

```lean
set_option maxHeartbeats 1000000 in
theorem exists_exactSource_evaluation_local_comparisons (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K N : schemeDerivedCategory X) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (_hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t))
    (_hdual : (localEvaluationDual X U P).IsKFlat)
    (_eK : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj P)
    (_eN : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj N ≅ DerivedCategory.Q.obj F)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (_hf : IsLocalOrdinaryEvaluation X U P F f) :
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory
    let H := derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf
    let D := H.obj (op K, 𝟙_ (schemeDerivedCategory X))
    let g := ((schemeDerivedTensorHomEquiv X) (N ⊗ D) K N).symm
      ((α_ N D K).hom ≫ N ◁
        ((schemeDerivedTensorHomEquiv X) D K (𝟙_ (schemeDerivedCategory X)) (𝟙 D)) ≫
          (ρ_ N).hom)
    ∃ a : R.obj (N ⊗ D) ≅ DerivedCategory.Q.obj (localEvaluationTensor X U P F),
      ∃ b : R.obj (H.obj (op K, N)) ≅
          DerivedCategory.Q.obj (homComplex (R := X.sheaf.over U) P F),
        R.map g ≫ b.hom = a.hom ≫ DerivedCategory.Q.map f
```

The body is proved from the two new calculation lemmas via the private proved
square-composition helper. No definition, target statement or public signature changes.
The option applies only to this declaration and changes no importer settings.

## Users

`tools/downstream.py --uses exists_exactSource_evaluation_local_comparisons` finds
only the following users of the declaration. The full import closure has 468 modules;
none requires adaptation because the statement and exported elaboration environment
remain identical. The two downstream proofs keep their current arguments and conclusions.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons | N4 | the local elaboration budget is raised; the signature is identical |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalRetraction | unclaimed | no change to arguments, statement or proof |
| Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalSection | unclaimed | no change to arguments, statement or proof |

## Status

landed 20261013T132737-L-4152183 2026-10-13 (merge of deliver/N4/Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons)
