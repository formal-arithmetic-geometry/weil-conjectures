/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalization
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationColimitTransport
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-! # Integral localization commutes with bounded qcqs derived pushforward -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The unit of `LY ⊣ UY` followed by the pushed mate of a comparison `κ : H ⋙ UY ≅ UX ⋙ G` is
`G` applied to the unit of `LX ⊣ UX`. -/
theorem mate_unit_comap
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {LX : A ⥤ B} {UX : B ⥤ A} {LY : C ⥤ D} {UY : D ⥤ C}
    (adjX : LX ⊣ UX) (adjY : LY ⊣ UY) {G : A ⥤ C} {H : B ⥤ D}
    (κ : H ⋙ UY ≅ UX ⋙ G) (K : A) :
    adjY.unit.app (G.obj K) ≫
        (UY.map ((Adjunction.pushHomOfComapIso adjX adjY κ).app K) ≫
          κ.hom.app (LX.obj K)) = G.map (adjX.unit.app K) := by
  have h := unit_mateEquiv_symm adjX adjY (TwoSquare.mk _ _ _ _ κ.inv) K
  change G.map (adjX.unit.app K) ≫ κ.inv.app (LX.obj K) =
    adjY.unit.app (G.obj K) ≫
      UY.map ((Adjunction.pushHomOfComapIso adjX adjY κ).app K) at h
  have hh := congrArg (fun z ↦ z ≫ κ.hom.app (LX.obj K)) h.symm
  simp only [Category.assoc, Iso.inv_hom_id_app] at hh
  exact hh.trans (Category.comp_id (G.map (adjX.unit.app K)))

/-- The zeroth legs of the localization-unit cocones of `adjY` at `G K` and of `G` applied to
that of `adjX` at `K` agree after a comparison `g` that is compatible with the units. -/
theorem localization_comparison_zero (ℓ : ℕ)
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {LX : A ⥤ B} {UX : B ⥤ A} {LY : C ⥤ D} {UY : D ⥤ C}
    [UX.Additive] [UY.Additive] (adjX : LX ⊣ UX) (adjY : LY ⊣ UY)
    (G : A ⥤ C) [G.Additive] (K : A)
    [IsIso (ℓ • 𝟙 (LX.obj K))] [IsIso (ℓ • 𝟙 (LY.obj (G.obj K)))]
    (g : UY.obj (LY.obj (G.obj K)) ⟶ G.obj (UX.obj (LX.obj K)))
    (hg : adjY.unit.app (G.obj K) ≫ g = G.map (adjX.unit.app K)) :
    (scalarLocalizationUnitCocone ℓ adjY (G.obj K)).ι.app 0 ≫ g =
      ((Cocone.precompose (Mod.smulSequenceCompIso G K ℓ).inv).obj
        (G.mapCocone (scalarLocalizationUnitCocone ℓ adjX K))).ι.app 0 := by
  simp only [scalarLocalizationUnitCocone, Functor.comp_obj, Functor.const_obj_obj, pow_zero,
    End.one_def, CategoryTheory.Functor.map_id, Category.comp_id, Mod.smulSequenceCompIso,
    NatIso.ofComponents_inv_app, Iso.refl_inv, Cocone.precompose_obj_pt, Functor.mapCocone_pt,
    Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.mapCocone_ι_app]
  change adjY.unit.app (G.obj K) ≫ g = 𝟙 _ ≫ G.map (adjX.unit.app K)
  exact hg.trans (Category.id_comp (G.map (adjX.unit.app K))).symm

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

end AlgebraicGeometry.ProEtale.CondensedRing
