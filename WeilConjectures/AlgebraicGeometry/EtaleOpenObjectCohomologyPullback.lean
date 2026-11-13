/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenFreeSheafPullback
import WeilConjectures.AlgebraicGeometry.EtaleOpenFreeSheafUnitPullback
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- The open-object map commutes with pullback of arbitrary Ext classes
(Stacks, Tags 03F3, 01F8 and 01FB). -/
theorem etaleOpenObjectCohomologyMap_pullback
    {X Y : Scheme.{u}} (g : Y ⟶ X) (W : X.Opens)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Abelian.Ext ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk W.ι)) G q) :
    etaleOpenObjectCohomologyMap ((upperStar AddCommGrpCat.{u + 1} g).obj G)
      q (g ⁻¹ᵁ W)
        ((Abelian.Ext.mk₀ (etaleOpenFreeSheafPullback g W)).comp
          (x.mapExactFunctor (upperStar AddCommGrpCat.{u + 1} g)) (zero_add q)) =
      openCohomologyPullback g W G q (etaleOpenObjectCohomologyMap G q W x)  := by
  let P := upperStar AddCommGrpCat.{u + 1} g
  let R := upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι
  let L := upperStar AddCommGrpCat.{u + 1} W.ι
  let T := upperStar AddCommGrpCat.{u + 1} (g ∣_ W)
  let H := upperStar AddCommGrpCat.{u + 1} ((g ⁻¹ᵁ W).ι ≫ g)
  let e₁ := upperStarComp AddCommGrpCat.{u + 1} (g ∣_ W) W.ι
    ((g ⁻¹ᵁ W).ι ≫ g) (morphismRestrict_ι g W).symm
  let e₂ := upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι g
  let k := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
    (g ∣_ W)).inv.app (AddCommGrpCat.of (ULift ℤ))
  change (Abelian.Ext.mk₀ (etaleOpenFreeSheafUnit (g ⁻¹ᵁ W))).comp
      (((Abelian.Ext.mk₀ (etaleOpenFreeSheafPullback g W)).comp
        (x.mapExactFunctor P) (zero_add q)).mapExactFunctor R) (zero_add q) =
    ((Abelian.Ext.mk₀ k).comp
      (((Abelian.Ext.mk₀ (etaleOpenFreeSheafUnit W)).comp
        (x.mapExactFunctor L) (zero_add q)).mapExactFunctor T) (zero_add q)).comp
      (Abelian.Ext.mk₀ ((e₁.inv ≫ e₂.hom).app G)) (add_zero q)
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀_assoc]
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀_assoc]
  rw [etaleOpenFreeSheafUnit_pullback]
  change (Abelian.Ext.mk₀ (k ≫ T.map (etaleOpenFreeSheafUnit W) ≫
      e₁.inv.app _ ≫ e₂.hom.app _)).comp
      ((x.mapExactFunctor P).mapExactFunctor R) (zero_add q) = _
  simp only [← Abelian.Ext.mk₀_comp_mk₀_assoc]
  rw [← Abelian.Ext.mapExactFunctor_comp_mk₀_eq_sheaf P R H e₂ x]
  have hc := congrArg
    (fun z ↦ ((Abelian.Ext.mk₀ (e₁.inv.app _)).comp z (zero_add q)).comp
      (Abelian.Ext.mk₀ (e₁.inv.app G)) (add_zero q))
    (Abelian.Ext.mapExactFunctor_comp_mk₀_eq_sheaf L T H e₁ x)
  simp only [← Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id_app,
    Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_mk₀_id,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    Iso.hom_inv_id_app] at hc
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero
    (Abelian.Ext.mk₀ (e₁.inv.app _)) (x.mapExactFunctor H)
    (Abelian.Ext.mk₀ (e₂.hom.app G)) (zero_add q), hc]
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀,
    NatTrans.comp_app]

end AlgebraicGeometry.Etale
