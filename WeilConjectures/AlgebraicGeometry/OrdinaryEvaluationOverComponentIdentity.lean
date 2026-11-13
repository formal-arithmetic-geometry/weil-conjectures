/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationComponent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.OpenModuleContractionTransport
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationOverDualProjection

/-! # Evaluation components with a fixed normalized tensor comparison

## References

* Stacks Project, Tag 0A8X, ordinary tensor totalization.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

noncomputable local instance ordinaryComponentIdentityOverPreadditive
    (X : Scheme.{u}) (U : X.Opens) :
    MonoidalPreadditive (localEvaluationModules X U) :=
  Classical.choice (SheafOfModules.tensorClosed (X.sheaf.over U)).1

noncomputable local instance ordinaryComponentIdentitySchemePreadditive (Y : Scheme.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1

attribute [local irreducible] homComplexFunctor Scheme.Modules.overEquiv
  Scheme.Modules.overEquivFunctorObjUnitIso HomologicalComplex.singleMapHomologicalComplex

set_option linter.unusedVariables false in
/-- The tensor-Hom component identity after dual and output transport
(Stacks, Tags 08DQ, 08DL and 0A8X). -/
theorem ordinaryEvaluation_over_component_identity (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    ∀ (e : ∀ A B : localEvaluationModules X U,
      L.obj
          (SheafOfModules.homObj (R := X.sheaf.over U) A B) ≅
        SheafOfModules.homObj (R := U.toScheme.sheaf)
          (L.obj A)
          (L.obj B))
    (he : ∀ (A A' B B' : localEvaluationModules X U) (f : A' ⟶ A) (g : B ⟶ B'),
      L.map
          (SheafOfModules.homObjMap (R := X.sheaf.over U) f g) ≫
          (e A' B').hom =
        (e A B).hom ≫ SheafOfModules.homObjMap (R := U.toScheme.sheaf)
          (L.map f)
          (L.map g))
    (b : ∀ M : CochainComplex (localEvaluationModules X U) ℤ,
      T.obj
          (homComplex (R := X.sheaf.over U) P M) ≅
        homComplex (R := U.toScheme.sheaf)
          (T.obj P)
          (T.obj M))
    (hπ : ∀ (M : CochainComplex (localEvaluationModules X U) ℤ)
          (n r s : ℤ) (h : r + n = s),
        (b M).hom.f n ≫
            (Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := U.toScheme.sheaf)))
              (T.obj P)
              (T.obj M)
              n r s h =
          L.map
            (localEvaluationProjection X U P M n r s h) ≫
            (e (P.X r) (M.X s)).hom),
    let a : T.obj (localEvaluationUnit X U) ≅
        (HomologicalComplex.single _ (.up ℤ) 0).obj
          (𝟙_ (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))) :=
      by
        set_option backward.isDefEq.respectTransparency true in
          exact (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).app _ ≪≫
            (HomologicalComplex.single _ (.up ℤ) 0).mapIso
              (Scheme.Modules.overEquivFunctorObjUnitIso U).symm
    let d := b (localEvaluationUnit X U) ≪≫
      ((homComplexFunctor.{u, u, u, u} (R := U.toScheme.sheaf)).obj (op (T.obj P))).mapIso a
    ∀ (m : L.CoreMonoidal)
      (_hunit : m.εIso = Scheme.Modules.overEquivFunctorObjUnitIso U)
      (_hsymm : ∀ A B : localEvaluationModules X U,
        L.map (β_ A B).hom ≫ (m.μIso B A).inv =
          (m.μIso A B).inv ≫ (β_ (L.obj A) (L.obj B)).hom)
      (F : CochainComplex (localEvaluationModules X U) ℤ)
      (p q n r : ℤ) (hpq : p + q = n),
      letI := SheafOfModules.monoidalCategory U.toScheme.sheaf
      letI := SheafOfModules.symmetricCategory U.toScheme.sheaf
      (𝟙 ((T.obj F).X p) ⊗ₘ d.inv.f q) ≫
        (m.μIso (F.X p) ((localEvaluationDual X U P).X q)).hom ≫
        L.map (localEvaluationComponent X U P F p q n r hpq) ≫
        (e (P.X r) (F.X (r + n))).hom =
      schemeOrdinaryEvaluationComponent U.toScheme (T.obj P) (T.obj F) p q n r hpq
        := by
  classical
  intro L T e he b hπ a d m hunit hsymm F p q n r hpq
  let := SheafOfModules.monoidalCategory U.toScheme.sheaf
  let := SheafOfModules.symmetricCategory U.toScheme.sheaf
  let : L.Full := (Scheme.Modules.overEquiv U).full_functor
  let : L.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full L
  by_cases h : r + q = 0
  · have hk : L.map (F.XIsoOfEq (by omega : p = r + n)).hom =
        ((T.obj F).XIsoOfEq (by omega : p = r + n)).hom := by
      have hh : p = r + n := by omega
      cases hh
      simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
      exact L.map_id _
    have hv := ordinaryEvaluation_over_dual_projection X U P e he b hπ q r h
    dsimp only [homComplex] at hv
    have hc := openModule_contraction_transport X U e he m hunit hsymm
      (P.X r) (F.X p) ((localEvaluationDual X U P).X q) (F.X (r + n))
      _ (d.inv.f q)
      (localEvaluationProjection X U P (localEvaluationUnit X U) q r 0 h ≫
        SheafOfModules.homObjMap (R := X.sheaf.over U) (𝟙 (P.X r))
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (𝟙_ (localEvaluationModules X U))).hom)
      (F.XIsoOfEq (by omega : p = r + n)).hom _ _ hv hk
    simp only [localEvaluationComponent, schemeOrdinaryEvaluationComponent, dite_eq_left h]
    dsimp only [homComplex]
    set_option backward.isDefEq.respectTransparency.types true in
      convert hc using 1 <;> congr 1
  · change _ ≫ _ ≫ L.map _ ≫ _ = _
    simp only [localEvaluationComponent, schemeOrdinaryEvaluationComponent, dite_eq_right h,
      Functor.map_zero, zero_comp]
    simp only [comp_zero]
end AlgebraicGeometry
