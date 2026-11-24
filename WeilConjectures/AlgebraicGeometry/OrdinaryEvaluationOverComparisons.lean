/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
import WeilConjectures.AlgebraicGeometry.HomComplexOverEquivProjections
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationOverTensorFormula

/-! # Compatible ordinary evaluation comparisons on the open scheme

No acyclicity, quasi-isomorphism or K-injectivity assertion is included here.

## References

* Stacks Project, Tags 08DL, 08DJ and 08DQ.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

-- The public existential dual witness is intentionally independent of the tensor witness.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency true in
-- Compare the chosen Hom bifunctors without unfolding their existence proofs.
/-- Compatible comparisons for ordinary Hom, its dual and ordinary evaluation
(Stacks, Tags 08DL, 08DJ and 08DQ). -/
theorem exists_ordinaryEvaluation_over_comparisons (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ) :
    let L := Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    let P' := T.obj P
    let O' := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))
    let D' := homComplex (R := U.toScheme.sheaf) P' O'
    ∃ b : ∀ M : CochainComplex (localEvaluationModules X U) ℤ,
        T.obj (homComplex (R := X.sheaf.over U) P M) ≅
          homComplex (R := U.toScheme.sheaf) P' (T.obj M),
      (∀ (M N : CochainComplex (localEvaluationModules X U) ℤ) (a : M ⟶ N),
        T.map (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map a) ≫
            (b N).hom =
          (b M).hom ≫
            ((homComplexFunctor (R := U.toScheme.sheaf)).obj (op P')).map (T.map a)) ∧
      ∃ d : T.obj (localEvaluationDual X U P) ≅ D',
        ∀ F : CochainComplex (localEvaluationModules X U) ℤ,
          ∃ t : T.obj (localEvaluationTensor X U P F) ≅
              pullbackTensorTotal U.toScheme (T.obj F) D',
            ∀ f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F,
              IsLocalOrdinaryEvaluation X U P F f →
                IsSchemeOrdinaryEvaluation U.toScheme P' (T.obj F)
                  (t.inv ≫ T.map f ≫ (b F).hom) := by
  classical
  let : MonoidalPreadditive
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed U.toScheme.sheaf).1
  dsimp only
  let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
  let T := L.mapHomologicalComplex (.up ℤ)
  have hTensor := exists_ordinaryEvaluation_over_tensor_formula X U P
  let e := Classical.choose hTensor
  have he := (Classical.choose_spec hTensor).1
  have hEval := (Classical.choose_spec hTensor).2
  have h := exists_homComplex_overEquiv_projections X U P e he
  let b := Classical.choose h
  have hb := (Classical.choose_spec h).1
  have hπ := (Classical.choose_spec h).2
  refine ⟨b, hb, ?_⟩
  let O' := (HomologicalComplex.single _ (.up ℤ) 0).obj
    (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))
  let a : T.obj (localEvaluationUnit X U) ≅ O' :=
    (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app _ ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso
        (Scheme.Modules.overEquivFunctorObjUnitIso U).symm
  let d : T.obj (localEvaluationDual X U P) ≅
      homComplex (R := U.toScheme.sheaf) (T.obj P) O' :=
    b (localEvaluationUnit X U) ≪≫
      ((homComplexFunctor (R := U.toScheme.sheaf)).obj (op (T.obj P))).mapIso a
  refine ⟨d, ?_⟩
  intro F
  have hF := hEval b hπ F
  let c := Classical.choose hF
  have hc := Classical.choose_spec hF
  let tensor := ((curriedTensor (SheafOfModules.{u}
    (moduleRings U.toScheme.toRingedSpace))).map₂CochainComplex).obj (T.obj F)
  exact ⟨c ≪≫ tensor.mapIso d, hc⟩

end AlgebraicGeometry
