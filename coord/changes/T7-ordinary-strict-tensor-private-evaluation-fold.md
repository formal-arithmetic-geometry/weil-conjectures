# WeilConjectures.scalarCoefficientEvaluation (private)

## Reason

The transition proof needs an API for the inverse evaluation on sections. Fold the
already constructed coefficient functor in its whiskering and give the equality
isomorphism a typed private wrapper. Both folds are definitionally equal to the
original expressions. The actual functor, evaluation isomorphism, tensor sections,
and public existence statement therefore have the same data and meaning.
The private proof API can then keep the sequence ring folded during elaboration.
The degreewise evaluation constructor uses Mathlib's
`Functor.mapHomologicalComplexCompIso` whiskered by the good-subcategory inclusion.
Its hom and inverse in degree `i` are the same components
`(scalarCoefficientEvaluation ... n).hom.app (P.obj.X i)` and its inverse.
This replaces the hand-built `NatIso.ofComponents` and `isoOfComponents` record
with the existing generic construction, reducing kernel normalization.

## Old

```lean
@[irreducible] private def scalarCoefficientEvaluation (n : ℕ) :
    scalarCoefficientExtension l E L ι W ⋙ coefficientSequenceEvaluation l L W n ≅
      integralScalarReduction l E L ι W n := by
  let F := SheafOfModules.SequenceProjection.extension
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W)
  let G := SheafOfModules.strictSystemToSequenceFunctor (coefficientSequenceCommRingSystem l L W)
  let B := coefficientSequenceCommRingSystem l L W
  let a : F ⋙ G ⋙ coefficientSequenceEvaluation l L W n ≅
      F ⋙ G ⋙ SheafOfModules.systemSequenceEvaluation B n :=
    Functor.isoWhiskerLeft (F ⋙ G) (eqToIso (coefficientEvaluation_eq_system l L W n))
  let b : F ⋙ G ⋙ SheafOfModules.systemSequenceEvaluation B n ≅
      F ⋙ SheafOfModules.systemEvaluation B n :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.strictSystemSequenceUnitLevel B
      (F.obj M) n).symm) (by intros; ext U x; rfl)
  let c : F ⋙ SheafOfModules.systemEvaluation B n ≅
      integralScalarReductionConcrete l E L ι W n :=
    NatIso.ofComponents (fun M ↦
      SheafOfModules.SequenceProjection.extensionIso
        (completedIntegralCommRingSheafUnrestricted l E W) B
          (scalarCoefficientCone l E L ι W) M n)
      (by
        intro M N f
        exact extensionIso_naturality
          (completedIntegralCommRingSheafUnrestricted l E W) B
          (scalarCoefficientCone l E L ι W) f n)
  exact a ≪≫ b ≪≫ c ≪≫ (integralScalarReductionIso l E L ι W n).symm
```

## New

```lean
private def coefficientEvaluationSystem (n : ℕ) :
    coefficientSequenceModules l L W ⥤ normalizedDVRModules l L W n :=
  SheafOfModules.systemSequenceEvaluation (coefficientSequenceCommRingSystem l L W) n

private theorem coefficientEvaluation_eq_foldedSystem (n : ℕ) :
    coefficientSequenceEvaluation l L W n = coefficientEvaluationSystem l L W n :=
  coefficientEvaluation_eq_system l L W n

private def coefficientEvaluationIso (n : ℕ) :
    coefficientSequenceEvaluation l L W n ≅ coefficientEvaluationSystem l L W n :=
  eqToIso (coefficientEvaluation_eq_foldedSystem l L W n)

@[irreducible] private def scalarCoefficientEvaluation (n : ℕ) :
    scalarCoefficientExtension l E L ι W ⋙ coefficientSequenceEvaluation l L W n ≅
      integralScalarReduction l E L ι W n := by
  let F := SheafOfModules.SequenceProjection.extension
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W)
  let G := SheafOfModules.strictSystemToSequenceFunctor (coefficientSequenceCommRingSystem l L W)
  let B := coefficientSequenceCommRingSystem l L W
  let a : F ⋙ G ⋙ coefficientSequenceEvaluation l L W n ≅
      F ⋙ G ⋙ SheafOfModules.systemSequenceEvaluation B n :=
    Functor.isoWhiskerLeft (scalarCoefficientExtension l E L ι W)
      (coefficientEvaluationIso l L W n)
  let b : F ⋙ G ⋙ SheafOfModules.systemSequenceEvaluation B n ≅
      F ⋙ SheafOfModules.systemEvaluation B n :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.strictSystemSequenceUnitLevel B
      (F.obj M) n).symm) (by intros; ext U x; rfl)
  let c : F ⋙ SheafOfModules.systemEvaluation B n ≅
      integralScalarReductionConcrete l E L ι W n :=
    NatIso.ofComponents (fun M ↦
      SheafOfModules.SequenceProjection.extensionIso
        (completedIntegralCommRingSheafUnrestricted l E W) B
          (scalarCoefficientCone l E L ι W) M n)
      (by
        intro M N f
        exact extensionIso_naturality
          (completedIntegralCommRingSheafUnrestricted l E W) B
          (scalarCoefficientCone l E L ι W) f n)
  exact a ≪≫ b ≪≫ c ≪≫ (integralScalarReductionIso l E L ι W n).symm
```

Unfolding `coefficientEvaluationSystem`, `coefficientEvaluationIso`, and
`scalarCoefficientExtension` recovers the old expression for `a`; the equality
proofs are equal by proof irrelevance. All other constructor fields and components
are identical.

The degreewise constructor is changed as follows.

Old:

```lean
private def scalarCoefficientDirectEvaluation (n : ℕ) :
    scalarCoefficientDirect l E L ι W ⋙
        (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
      (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n :=
  NatIso.ofComponents (fun P ↦ HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (scalarCoefficientEvaluation l E L ι W n).app (P.obj.X i))
    (by
      intro i j hij
      exact ((scalarCoefficientEvaluation l E L ι W n).hom.naturality (P.obj.d i j)).symm))
    (by
      intro P Q f
      apply HomologicalComplex.hom_ext
      intro i
      exact (scalarCoefficientEvaluation l E L ι W n).hom.naturality (f.hom.f i))
```

New:

```lean
private def scalarCoefficientDirectEvaluation (n : ℕ) :
    scalarCoefficientDirect l E L ι W ⋙
        (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
      (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n := by
  unfold scalarCoefficientDirect
  exact Functor.isoWhiskerLeft (integralOperationsGoodComplex l E W).ι
    (Functor.mapHomologicalComplexCompIso (scalarCoefficientEvaluation l E L ι W n) (.up ℤ))
```

The cone keeps exactly its original components `integralScalarRho`. Its
naturality proof now applies the existing private theorem
`integralScalarRho_transition` via a private `import all` of the same dependency.
Proof irrelevance preserves the cone data.

Old:

```lean
private def scalarCoefficientCone :
    (Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W) ⟶
      coefficientSequenceCommRingSystem l L W :=
  NatTrans.ofOpSequence (fun n ↦ integralScalarRho l E L ι W n) (fun n ↦ by
    simp only [Functor.const_obj_map,
      coefficientSequenceCommRingSystem, Functor.ofOpSequence_map_homOfLE_succ]
    unfold integralScalarRho
    rw [Category.assoc, coefficientExtensionQuotient_naturality]
    erw [Category.id_comp]
    rw [← Category.assoc]
    apply congrArg (fun f ↦ f ≫ integralScalarQuotientSheafMap l E L ι W n)
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply (forget₂ CommRingCat RingCat).map_injective
    change (limit.π (integralCoefficientSheafSystem l E W) (op n)).hom.app U =
      (limit.π (integralCoefficientSheafSystem l E W) (op (n + 1))).hom.app U ≫
        (integralCoefficientSheafTransition l E W n).hom.app U
    have h := congrArg (fun k ↦ k.hom.app U)
      (limit.w (integralCoefficientSheafSystem l E W) (homOfLE (Nat.le_succ n)).op)
    simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using h.symm)
```

New:

```lean
private def scalarCoefficientCone :
    (Functor.const ℕᵒᵖ).obj (completedIntegralCommRingSheafUnrestricted l E W) ⟶
      coefficientSequenceCommRingSystem l L W :=
  NatTrans.ofOpSequence (fun n ↦ integralScalarRho l E L ι W n) (fun n ↦ by
    simp only [Functor.const_obj_map, coefficientSequenceCommRingSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact (integralScalarRho_transition l E L ι W n).symm)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientExtensionOrdinaryStrictTensor | T7 | Private evaluation constructor and proved section API; its degreewise consumer keeps the same signature. |
| Sheaf.Paper.CoefficientExtensionStrictRepresentatives | unclaimed | Uses only the unchanged public existence theorem; no adaptation. |

Source inspection finds no external use of this private declaration. The sole
importer is `CoefficientExtensionStrictRepresentatives`; it applies the public
existence theorem. The local `downstream.py` scanner also invokes git and writes
caches, so it is not run in this read-only clone under the remote-worker brief.
The delivery's server checks can perform the standard downstream audit.

## Status

landed 20261026T092712-L-3454742 2026-10-26 (merge of deliver/T7/Sheaf.Paper.CoefficientExtensionOrdinaryStrictTensor)
