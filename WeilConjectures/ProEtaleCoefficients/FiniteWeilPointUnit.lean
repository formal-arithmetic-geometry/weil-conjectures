/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.WeilObject.Sheaf.StalkUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
/-! # Unit normalization for the canonical restriction on a separably closed point

(blueprint: lem-finite-weil-point-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures
private theorem finiteWeilDerivedIdIso_eq
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [MonoidalCategory A] [MonoidalPreadditive A] [HasCountableCoproducts A]
    [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ X : A, PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
    [∀ X : A, PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution A]
    (F : A ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 A) :
    Functor.leftDerivedFunctorIdIso e =
      F.leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryNatIso e ≪≫
        Functor.mapDerivedCategoryIdIso A := by
  apply Iso.ext
  simp only [Functor.leftDerivedFunctorIdIso, Functor.leftDerivedFunctorNatIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

set_option maxHeartbeats 1600000 in
-- Keep the natural isomorphism abstract during the native unit calculation.
private theorem finiteWeilNativeUnit_of_underived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (g : X ⟶ X)
    (e : upperStar Λ g ≅ 𝟭 _)
    (he : e.hom.app _ = (Functor.Monoidal.εIso (upperStar Λ g)).inv) :
    (leftDerivedUpperStarIsoMapDerivedCategory Λ g ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _).hom.app _ =
      (leftDerivedUpperStarUnitIso Λ g).hom := by
  unfold CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
  rw [← finiteWeilDerivedIdIso_eq (upperStar Λ g) e,
    CondensedRing.leftDerivedUpperStarUnitIso_hom_eq, ← he,
    ← Functor.mapHomotopyCategorySingleHom_id]
  exact Functor.leftDerivedFunctorIdIso_hom_app_Qh_obj e (𝟙_ _)


set_option maxHeartbeats 200000 in
-- Generalize the concrete point iso before comparing its unit components.
/-- The canonical restriction on a separably closed point agrees with native pullback on units.

Source: latest blueprint lem-fix-weil-operations-finite.proof, Step 8;
upstream StalkUnit and UpperStarUnitCoherence.
(blueprint: lem-finite-weil-point-unit).

Proof:
1. The underived restriction isomorphism has unit component equal to the inverse
   monoidal unit map, by upperStarIsoIdOfIsSepClosed_hom_app_unit.
2. Keep that isomorphism abstract. Exact-to-derived unit coherence expresses the derived
   unit as the derived-single image of this component after the exact comparison.
3. The derived identity comparison has the same component by the single-object formula
   for leftDerivedFunctorIdIso. Expand its defining composite and cancel the exact
   comparison isomorphism. Specializing to the canonical point restriction gives the
   displayed equality. No nonzero coefficient or nonempty auxiliary scheme is used. -/
theorem finiteWeilPointUnitComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {k : Type u} [Field k] [IsSepClosed k]
    (g : Spec (.of k) ≅ Spec (.of k)) :
    (leftDerivedUpperStarIsoMapDerivedCategory Λ g.hom ≪≫
      Functor.mapDerivedCategoryNatIso (upperStarIsoIdOfIsSepClosed Λ g.hom) ≪≫
      Functor.mapDerivedCategoryIdIso _).hom.app _ =
      (leftDerivedUpperStarUnitIso Λ g.hom).hom := by
  have he := upperStarIsoIdOfIsSepClosed_hom_app_unit Λ g.hom
  generalize hτ : upperStarIsoIdOfIsSepClosed Λ g.hom = τ at he ⊢
  exact finiteWeilNativeUnit_of_underived Λ g.hom τ he

end WeilConjectures
