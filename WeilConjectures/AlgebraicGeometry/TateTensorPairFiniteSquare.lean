/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedTateIntegralTowerData
import WeilConjectures.AlgebraicGeometry.TateTensorFiniteTransition
import WeilConjectures.AlgebraicGeometry.TateTensorBalancedTransition
import WeilConjectures.CategoryTheory.ExactSingleTransformation

/-! Single-model transport of the ordinary finite Tate transition square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

attribute [local irreducible] HasDerivedCategory.standard Functor.leftAdjoint
  SheafOfModules.monoidalCategory completedAdicDerivedChange finiteModelIso

/-- Canonical finite single model followed by a chosen ordinary quotient identification.
Source: normalized Tate tower, Step 4.
(blueprint: def-pur-tate-tensor-pair-evaluation-model) -/
def finiteEvaluationModel
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d n : ℕ)
    (c : (realization T ell n).obj (finiteSheaf T ell n d) ≅ quotientLine T ell n d) :
    (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) n)).obj
        ((derivedRealization T ell n).obj (finiteTwist T ell n d)) ≅
      (pbcTowerEvaluation T (pbcAdicCompletion T (datum.{u} ell)) n).obj
        (strictDerivedTower T ell d) :=
  (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) n)).mapIso
      (finiteModelIso T ell hT n d) ≪≫
    (Functor.mapDerivedCategorySingleFunctor
      (pbcRestrict (pbcAdicProjection T (datum.{u} ell) n)) (-(2 * (d : ℤ)))).app _ ≪≫
    (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).mapIso
      ((pbcRestrict (pbcAdicProjection T (datum.{u} ell) n)).mapIso c) ≪≫
    (Functor.mapDerivedCategorySingleFunctor
      ((CategoryTheory.evaluation ℕᵒᵖ
        (pbcModules T (pbcAdicCompletion T (datum.{u} ell)))).obj (op n))
      (-(2 * (d : ℤ)))).symm.app (strictTower T ell d)

private theorem single_transition_assembly
    {A D : Type*} [Category A] [Category D] (F : A ⥤ D)
    {x y u v : A} (f : x ⟶ y) (cb : x ⟶ u) (ca : y ⟶ v) (t : u ⟶ v)
    {Mb Ma Eb Ea : D} (pb : Mb ⟶ F.obj x) (pa : Ma ⟶ F.obj y)
    (δ : Mb ⟶ Ma) (eb : Eb ≅ F.obj u) (ea : Ea ≅ F.obj v) (s : Eb ⟶ Ea)
    (hmodel : δ ≫ pa = pb ≫ F.map f)
    (hord : f ≫ ca = cb ≫ t) (ht : s ≫ ea.hom = eb.hom ≫ F.map t) :
    δ ≫ pa ≫ F.map ca ≫ ea.inv = pb ≫ F.map cb ≫ eb.inv ≫ s := by
  have ht' : F.map t ≫ ea.inv = eb.inv ≫ s := by
    apply (cancel_epi eb.hom).1
    rw [← Category.assoc, ← ht]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  calc
    δ ≫ pa ≫ F.map ca ≫ ea.inv = pb ≫ F.map f ≫ F.map ca ≫ ea.inv := by
      rw [reassoc_of% hmodel]
    _ = pb ≫ F.map cb ≫ F.map t ≫ ea.inv := by
      rw [← F.map_comp_assoc, hord, F.map_comp, Category.assoc]
    _ = pb ≫ F.map cb ≫ eb.inv ≫ s := by rw [ht']

/-- The finite scalar mate square on the chosen balanced quotient models.
Source: normalized Tate tower, Step 4.
(blueprint: lem-pur-tate-tensor-pair-finite-square)

Proof: represent the finite scalar mate by its ordinary root transition, apply the
ordinary balanced-transition square, then transport through the exact single
comparisons. The strict tower transition on a single is the single of the
ordinary transition by exactSingle_transformation. -/
theorem finite_transition_square
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d b a : ℕ) (hab : a ≤ b)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)
    (cb : (realization T ell b).obj (finiteSheaf T ell b d) ≅ quotientLine T ell b d)
    (ca : (realization T ell a).obj (finiteSheaf T ell a d) ≅ quotientLine T ell a d)
    (hb : ProjectionBalanced T ell b d cb) (ha : ProjectionBalanced T ell a d ca) :
    (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) b)).map
        ((pbcDerivedScalarAdjunction (pbcAdicQuotient T (datum.{u} ell) b a hab)).homEquiv
          _ _ ((scalarComparison T ell b a hab).hom.app (finiteTwist T ell b d) ≫
            (derivedRealization T ell a).map (proTwistMap d r))) ≫
      (pbcDerivedRestrictComp (pbcAdicProjection T (datum.{u} ell) b)
        (pbcAdicQuotient T (datum.{u} ell) b a hab)
        (pbcAdicProjection T (datum.{u} ell) a)
        (pbcAdicProjection_comp T (datum.{u} ell) b a hab)).hom.app _ ≫
      (finiteEvaluationModel T ell hT d a ca).hom =
    (finiteEvaluationModel T ell hT d b cb).hom ≫
      (pbcTowerTransition T (pbcAdicCompletion T (datum.{u} ell)) b a hab).app
        (strictDerivedTower T ell d) := by
  obtain ⟨f, hf, hmodel⟩ := finiteTateTensor_transition_model T ell hT d b a hab r
  have hord := tateTensor_balanced_transition T ell hT d b a hab r f hf cb ca hb ha
  have ht := SheafProject.exactSingle_transformation
    ((CategoryTheory.evaluation ℕᵒᵖ
      (pbcModules T (pbcAdicCompletion T (datum.{u} ell)))).obj (op b))
    ((CategoryTheory.evaluation ℕᵒᵖ
      (pbcModules T (pbcAdicCompletion T (datum.{u} ell)))).obj (op a))
    ((CategoryTheory.evaluation ℕᵒᵖ
      (pbcModules T (pbcAdicCompletion T (datum.{u} ell)))).map (homOfLE hab).op)
    (-(2 * (d : ℤ))) (strictTower T ell d)
  have hg := single_transition_assembly
    (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))) f
    ((pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)).map cb.hom)
    ((pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)).map ca.hom)
    ((strictTower T ell d).map (homOfLE hab).op)
    ((pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) b)).map
        (finiteModelIso T ell hT b d).hom ≫
      (Functor.mapDerivedCategorySingleFunctor
        (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b))
        (-(2 * (d : ℤ)))).hom.app _)
    ((pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) a)).map
        (finiteModelIso T ell hT a d).hom ≫
      (Functor.mapDerivedCategorySingleFunctor
        (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a))
        (-(2 * (d : ℤ)))).hom.app _)
    ((pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) b)).map
        ((pbcDerivedScalarAdjunction (pbcAdicQuotient T (datum.{u} ell) b a hab)).homEquiv
          _ _ ((scalarComparison T ell b a hab).hom.app (finiteTwist T ell b d) ≫
            (derivedRealization T ell a).map (proTwistMap d r))) ≫
      (pbcDerivedRestrictComp (pbcAdicProjection T (datum.{u} ell) b)
        (pbcAdicQuotient T (datum.{u} ell) b a hab)
        (pbcAdicProjection T (datum.{u} ell) a)
        (pbcAdicProjection_comp T (datum.{u} ell) b a hab)).hom.app _)
    ((Functor.mapDerivedCategorySingleFunctor
      ((CategoryTheory.evaluation ℕᵒᵖ
        (pbcModules T (pbcAdicCompletion T (datum.{u} ell)))).obj (op b))
      (-(2 * (d : ℤ)))).app (strictTower T ell d))
    ((Functor.mapDerivedCategorySingleFunctor
      ((CategoryTheory.evaluation ℕᵒᵖ
        (pbcModules T (pbcAdicCompletion T (datum.{u} ell)))).obj (op a))
      (-(2 * (d : ℤ)))).app (strictTower T ell d))
    ((pbcTowerTransition T (pbcAdicCompletion T (datum.{u} ell)) b a hab).app
      (strictDerivedTower T ell d))
    (by simpa only [Category.assoc] using hmodel) hord ht
  simpa only [finiteEvaluationModel, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, Iso.app_inv, Category.assoc] using hg

end AlgebraicGeometry.Scheme.PurityIntegralTower
