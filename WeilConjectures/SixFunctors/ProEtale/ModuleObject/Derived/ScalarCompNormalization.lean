/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp

/-! Scalar transitivity counit normalization. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
  Mod.derivedExtendMapDerivedCategoryAdjunction

set_option maxHeartbeats 2000000 in
-- Comparing the internal module-object derived functors needs this elaboration budget.
set_option synthInstance.maxHeartbeats 200000 in
/-- The chosen derived scalar transitivity isomorphism respects the resolution counits.

Source: the scalar mate normalization in proof step 2 of
`lem-sp-original-integral-finite-quotient-mate-transport`, above the direct-image exchange
of the latest blueprint `def-exchange-projection`.

Proof in words. The underived comparison is uniqueness of left adjoints, so its unit
identity follows from `unit_leftAdjointUniq_hom_app`. Transport this identity to homotopy
categories. The exact restriction comparison is normalized on Qh by the localization
factorization equations. Apply the derived scalar adjunction to the desired equality,
use the unit identity for the conjugate transitivity map, and move the restriction
comparison through the counits by naturality. The formulas for the derived scalar units
then reduce the result to the underived unit identity. No flatness is required.
The calculation also applies to zero rings and zero complexes.
(blueprint: lem-sp-scalar-comp-normalization) -/
theorem scalarCompNormalization
    {U : Scheme.{u}} {R S T : Sheaf (ProEt.topology U) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    [MonObj T] [IsCommMonObj T]
    (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ]
    (K : HomotopyCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) R) (.up ℤ)) :
    (Mod.derivedExtendScalarsCompIso φ ψ (φ ≫ ψ) rfl).hom.app
        (DerivedCategory.Qh.obj K) ≫
      L(Mod.extendScalars ψ).map ((Mod.extendScalars φ).leftDerivedFunctorCounit.app K) ≫
      (Mod.extendScalars ψ).leftDerivedFunctorCounit.app
        (((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj K) =
    (Mod.extendScalars (φ ≫ ψ)).leftDerivedFunctorCounit.app K ≫
      DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory (Mod.extendScalarsComp φ ψ).hom (.up ℤ)).app K ≫
          (Functor.mapHomotopyCategoryCompIso
            (Iso.refl (Mod.extendScalars φ ⋙ Mod.extendScalars ψ)) (.up ℤ)).inv.app K) := by
  have hu (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) R) :
      (Mod.extendRestrictAdjunction (φ ≫ ψ)).unit.app M ≫
        (Mod.comap (φ ≫ ψ)).map ((Mod.extendScalarsComp φ ψ).hom.app M) =
      ((Mod.extendRestrictAdjunction φ).comp (Mod.extendRestrictAdjunction ψ)).unit.app M ≫
        (Mod.comapComp φ ψ).inv.app
          ((Mod.extendScalars φ ⋙ Mod.extendScalars ψ).obj M) := by
    exact Adjunction.unit_leftAdjointUniq_hom_app
      (Mod.extendRestrictAdjunction (φ ≫ ψ))
      (((Mod.extendRestrictAdjunction φ).comp
        (Mod.extendRestrictAdjunction ψ)).ofNatIsoRight (Mod.comapComp φ ψ).symm) M
  have hU := Adjunction.mapHomotopyCategory_unit_app_comp (.up ℤ)
    (Mod.extendRestrictAdjunction (φ ≫ ψ))
    ((Mod.extendRestrictAdjunction φ).comp (Mod.extendRestrictAdjunction ψ))
    (Mod.extendScalarsComp φ ψ).hom (Mod.comapComp φ ψ).inv hu K
  rw [Adjunction.mapHomotopyCategory_comp_unit_app] at hU
  have he (M : HomotopyCategory (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) T) (.up ℤ)) :
      (Mod.comap φ).mapDerivedCategoryFactorsh.inv.app
          (((Mod.comap ψ).mapHomotopyCategory (.up ℤ)).obj M) ≫
        D(Mod.comap φ).map ((Mod.comap ψ).mapDerivedCategoryFactorsh.inv.app M) ≫
        (Mod.mapDerivedCategoryComapCompIso φ ψ (φ ≫ ψ) rfl).hom.app
          (DerivedCategory.Qh.obj M) =
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Mod.comap ψ ⋙ Mod.comap φ)) (.up ℤ)).hom.app M ≫
          (NatTrans.mapHomotopyCategory (Mod.comapComp φ ψ).inv (.up ℤ)).app M) ≫
        (Mod.comap (φ ≫ ψ)).mapDerivedCategoryFactorsh.inv.app M := by
    have hf := Functor.mapDerivedCategoryCompIso_fach (Mod.comap ψ) (Mod.comap φ) M
    have hn := Functor.mapDerivedCategoryNatIso_fach (Mod.comapComp φ ψ).symm M
    have hc : Mod.comapCongr (rfl : φ ≫ ψ = φ ≫ ψ) = Iso.refl _ := by
      exact Iso.ext (NatTrans.ext (funext fun M ↦
        Mod.hom_ext _ _ (Mod.comapCongr_hom_app_hom rfl M)))
    simp only [Mod.mapDerivedCategoryComapCompIso, hc, Iso.trans_refl,
      Iso.trans_hom, NatTrans.comp_app]
    rw [← cancel_mono ((Mod.comap (φ ≫ ψ)).mapDerivedCategoryFactorsh.hom.app M)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [hn, ← hf]
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
    rw [Functor.map_comp]
    exact (Category.comp_id _).symm
  have hs :
      ((Mod.derivedExtendMapDerivedCategoryAdjunction φ).comp
        (Mod.derivedExtendMapDerivedCategoryAdjunction ψ)).unit.app
          (DerivedCategory.Qh.obj K) ≫
        (D(Mod.comap ψ) ⋙ D(Mod.comap φ)).map
          (L(Mod.extendScalars ψ).map
            ((Mod.extendScalars φ).leftDerivedFunctorCounit.app K) ≫
            (Mod.extendScalars ψ).leftDerivedFunctorCounit.app
              (((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj K)) =
      DerivedCategory.Qh.map
        (((Mod.extendRestrictAdjunction φ).mapHomotopyCategory (.up ℤ)).unit.app K) ≫
        (Mod.comap φ).mapDerivedCategoryFactorsh.inv.app
          (((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj K) ≫
        D(Mod.comap φ).map
          (DerivedCategory.Qh.map
            (((Mod.extendRestrictAdjunction ψ).mapHomotopyCategory (.up ℤ)).unit.app
              (((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj K))) ≫
        D(Mod.comap φ).map
          ((Mod.comap ψ).mapDerivedCategoryFactorsh.inv.app
            (((Mod.extendScalars ψ).mapHomotopyCategory (.up ℤ)).obj
              (((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj K))) := by
    simp only [Adjunction.comp_unit_app, Functor.map_comp, Functor.comp_map, Category.assoc]
    rw [← Functor.map_comp_assoc]
    have hn := (Mod.derivedExtendMapDerivedCategoryAdjunction ψ).unit.naturality
      ((Mod.extendScalars φ).leftDerivedFunctorCounit.app K)
    simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
    rw [← hn]
    rw [Functor.map_comp]
    simp only [Category.assoc]
    rw [Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh_assoc]
    rw [← Functor.map_comp, Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh]
    simp only [Functor.map_comp]
  apply ((Mod.derivedExtendMapDerivedCategoryAdjunction (φ ≫ ψ)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hc := unit_conjugateEquiv_symm
    ((Mod.derivedExtendMapDerivedCategoryAdjunction φ).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction ψ))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (φ ≫ ψ))
    (Mod.mapDerivedCategoryComapCompIso φ ψ (φ ≫ ψ) rfl).hom
    (DerivedCategory.Qh.obj K)
  change _ = (Mod.derivedExtendMapDerivedCategoryAdjunction (φ ≫ ψ)).unit.app _ ≫
    D(Mod.comap (φ ≫ ψ)).map
      ((Mod.derivedExtendScalarsCompIso φ ψ (φ ≫ ψ) rfl).hom.app _) at hc
  rw [← reassoc_of% hc]
  rw [← (Mod.mapDerivedCategoryComapCompIso φ ψ (φ ≫ ψ) rfl).hom.naturality_assoc,
    ← (Mod.mapDerivedCategoryComapCompIso φ ψ (φ ≫ ψ) rfl).hom.naturality]
  simp only [Functor.map_comp, Functor.comp_map] at hs ⊢
  rw [reassoc_of% hs]
  rw [Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_Qh_assoc]
  have hn := (Mod.comap φ).mapDerivedCategoryFactorsh.inv.naturality
    (((Mod.extendRestrictAdjunction ψ).mapHomotopyCategory (.up ℤ)).unit.app
      (((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj K))
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn]
  dsimp only [Functor.comp_obj] at he ⊢
  erw [he]
  have hn' := (Mod.comap (φ ≫ ψ)).mapDerivedCategoryFactorsh.inv.naturality
    ((NatTrans.mapHomotopyCategory (Mod.extendScalarsComp φ ψ).hom (.up ℤ)).app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn'
  rw [← reassoc_of% hn']
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  have hUi := congrArg DerivedCategory.Qh.map hU
  simp only [Functor.map_comp, Category.assoc,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app] at hUi ⊢
  repeat' first
    | erw [CategoryTheory.Functor.map_id] at hUi
    | erw [Category.id_comp] at hUi
  repeat' first
    | erw [CategoryTheory.Functor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]
  erw [← reassoc_of% hUi]
  rfl



end AlgebraicGeometry.ProEtale.CondensedRing
