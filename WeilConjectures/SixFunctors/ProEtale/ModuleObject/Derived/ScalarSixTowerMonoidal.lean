/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTowerNormalization
import WeilConjectures.CategoryTheory.DerivedScalarTensorCoherence
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidalComp
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidalComp
/-! # Monoidality of the canonical scalar tower -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor DerivedCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing
set_option maxHeartbeats 2000000 in
-- Compare the canonical tower through the derived counits and tensor universal property.
/-- The canonical adjunction-defined scalar associator is monoidal for ordinary derived
scalar extension, without restrictions on the ground field or coefficient maps.
Source: K-flat tensor associativity (blueprint: lem-sf-scalar-tower-monoidal).
Proof: ordinary restriction transitivity is monoidal. Its adjunction conjugate, ordinary
extension transitivity, is therefore monoidal. Pass its tensor identity to homotopy categories.
The scalar tower counit computation and the two-variable derived universal property give the
tensor identity on derived categories. For invertible tensor comparisons that identity also
determines the unit comparison, proving monoidality. -/
theorem scalarSixTower_monoidal {Λ₀ Λ₁ Λ₂ : ScalarSixRing.{u}}
    (a : Λ₀ ⟶ Λ₁) (b : Λ₁ ⟶ Λ₂) (X : Scheme.{u}) :
    NatTrans.IsMonoidal (scalarSixTower a b X).hom := by
  let F := Mod.extendScalars (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X) a.hom.hom X)
  let G := Mod.extendScalars (coefficientMap (Λ := Λ₁.X) (Λ' := Λ₂.X) b.hom.hom X)
  let H := Mod.extendScalars (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₂.X) (a ≫ b).hom.hom X)
  let := Mod.extendScalarsMonoidal (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X) a.hom.hom X)
  let := Mod.extendScalarsMonoidal (coefficientMap (Λ := Λ₁.X) (Λ' := Λ₂.X) b.hom.hom X)
  let := Mod.extendScalarsMonoidal (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₂.X) (a ≫ b).hom.hom X)
  let := Mod.comapLaxMonoidal (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X) a.hom.hom X)
  let := Mod.comapLaxMonoidal (coefficientMap (Λ := Λ₁.X) (Λ' := Λ₂.X) b.hom.hom X)
  let := Mod.comapLaxMonoidal (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₂.X) (a ≫ b).hom.hom X)
  let := Mod.comapLaxMonoidal
    (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X) a.hom.hom X ≫
      coefficientMap (Λ := Λ₁.X) (Λ' := Λ₂.X) b.hom.hom X)
  let := Mod.comapLaxMonoidal
    (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₂.X) (a.hom.hom ≫ b.hom.hom) X)
  have := Mod.isMonoidal_extendRestrictAdjunction
    (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X) a.hom.hom X)
  have := Mod.isMonoidal_extendRestrictAdjunction
    (coefficientMap (Λ := Λ₁.X) (Λ' := Λ₂.X) b.hom.hom X)
  have := Mod.isMonoidal_extendRestrictAdjunction
    (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₂.X) (a ≫ b).hom.hom X)
  have := Mod.isMonoidal_comapCongr_hom
    (coefficientMap_comp (Λ := Λ₀.X) (Λ' := Λ₁.X) (Λ'' := Λ₂.X)
      a.hom.hom b.hom.hom X)
  have := Mod.isMonoidal_comapComp_hom
    (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X) a.hom.hom X)
    (coefficientMap (Λ := Λ₁.X) (Λ' := Λ₂.X) b.hom.hom X)
  have hcomp : NatTrans.IsMonoidal
      (Mod.comapCongr (C := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (coefficientMap_comp (Λ := Λ₀.X) (Λ' := Λ₁.X) (Λ'' := Λ₂.X)
            a.hom.hom b.hom.hom X) ≪≫
        Mod.comapComp
          (coefficientMap (Λ := Λ₀.X) (Λ' := Λ₁.X) a.hom.hom X)
          (coefficientMap (Λ := Λ₁.X) (Λ' := Λ₂.X) b.hom.hom X)).hom := by
    simp only [Iso.trans_hom]
    infer_instance
  have he : NatTrans.IsMonoidal (scalarSixOrdinaryTower a b X).hom := by
    unfold scalarSixOrdinaryTower
    exact isMonoidal_conjugateEquiv_symm _ _ _
  have he' : NatTrans.IsMonoidal (scalarSixOrdinaryTower a b X).inv := inferInstance
  have hδ (P Q) : OplaxMonoidal.δ H P Q ≫
      ((scalarSixOrdinaryTower a b X).inv.app P ⊗ₘ
        (scalarSixOrdinaryTower a b X).inv.app Q) =
      (scalarSixOrdinaryTower a b X).inv.app (P ⊗ Q) ≫
        G.map (OplaxMonoidal.δ F P Q) ≫ OplaxMonoidal.δ G _ _ := by
    change OplaxMonoidal.δ H P Q ≫
      ((scalarSixOrdinaryTower a b X).inv.app P ⊗ₘ
        (scalarSixOrdinaryTower a b X).inv.app Q) =
      (scalarSixOrdinaryTower a b X).inv.app (P ⊗ Q) ≫ OplaxMonoidal.δ (F ⋙ G) P Q
    apply (cancel_mono (LaxMonoidal.μ (F ⋙ G) P Q)).mp
    simp only [Category.assoc]
    rw [← NatTrans.IsMonoidal.tensor, Functor.Monoidal.δ_μ_assoc,
      Functor.Monoidal.δ_μ, Category.comp_id]
  have hk (P Q) := Functor.mapHomotopyCategory_δ_comp_tensorHom
    (e := (scalarSixOrdinaryTower a b X).symm) hδ P Q
  have hδscalar {Γ Γ' : ScalarSixRing.{u}} (c : Γ ⟶ Γ')
      (P Q : DerivedCategory (ModuleRingedComparison.internalModules Γ.X X)) :
      letI := Mod.extendScalarsMonoidal
        (coefficientMap (Λ := Γ.X) (Λ' := Γ'.X) c.hom.hom X)
      OplaxMonoidal.δ (scalarSixChange c X) P Q =
        ((Mod.extendScalars
          (coefficientMap (Λ := Γ.X) (Λ' := Γ'.X) c.hom.hom X)).leftDerivedTensorComparison.app
            P).app Q := by
    let := Mod.extendScalarsMonoidal
      (coefficientMap (Λ := Γ.X) (Λ' := Γ'.X) c.hom.hom X)
    exact (Mod.extendScalars
      (coefficientMap (Λ := Γ.X) (Λ' := Γ'.X) c.hom.hom X)).leftDerivedFunctorMonoidal_δ P Q
  apply NatTrans.IsMonoidal.of_isIso_of_δ (scalarSixTower a b X).hom
  intro K M
  rw [Functor.OplaxMonoidal.comp_δ, hδscalar, hδscalar, hδscalar]
  simp only [Category.assoc]
  change (scalarSixTower a b X).hom.app (K ⊗ M) ≫
      (H.leftDerivedTensorComparison.app K).app M =
    G.leftDerivedFunctor.map ((F.leftDerivedTensorComparison.app K).app M) ≫
      (G.leftDerivedTensorComparison.app (F.leftDerivedFunctor.obj K)).app
        (F.leftDerivedFunctor.obj M) ≫ _
  apply derivedTensorComparison_of_normalization F G H (scalarSixHomotopyTower a b X)
  · intro P Q
    have hi (P) : (scalarSixHomotopyTower a b X).inv.app P =
        Functor.mapHomotopyCategoryCompHom F G H
          (scalarSixOrdinaryTower a b X).symm P := by
      obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
      change (HomotopyCategory.quotient _ (.up ℤ)).map _ =
        (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
          (HomotopyCategory.quotient _ (.up ℤ)).map _
      rw [← Functor.map_comp]
      congr 1
    have h := hk P Q
    rw [← hi P, ← hi Q, ← hi (P ⊗ Q)] at h
    apply (cancel_epi ((scalarSixHomotopyTower a b X).inv.app (P ⊗ Q))).mp
    simp only [Iso.inv_hom_id_app_assoc]
    rw [← reassoc_of% h]
    simp only [H, tensorHom_comp_tensorHom, Iso.inv_hom_id_app,
      id_tensorHom_id, Category.comp_id]
  · exact scalarSixTower_counit a b X
end AlgebraicGeometry.ProEtale.CondensedRing
