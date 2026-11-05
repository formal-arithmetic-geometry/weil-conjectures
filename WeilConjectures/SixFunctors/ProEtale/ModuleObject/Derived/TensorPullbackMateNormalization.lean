/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullMate
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MateCounit
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompNatIsoCounit

/-! Native condensed tensor/pullback mate normalization.
The fully proved scalar transitivity and derived normalization calculations are reused
from the main-tree proofs; no deleted interface module is imported or restored. -/

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

Source: the final associativity/counit compatibility paragraph of the latest blueprint's
`lem-fix-compact-support-coefficient-change`.

Proof in words. The underived comparison is uniqueness of left adjoints, so its unit
identity follows from `unit_leftAdjointUniq_hom_app`. Transport this identity to homotopy
categories. The exact restriction comparison is normalized on Qh by the localization
factorization equations. Apply the derived scalar adjunction to the desired equality,
use the unit identity for the conjugate transitivity map, and move the restriction
comparison through the counits by naturality. The formulas for the derived scalar units
then reduce the result to the underived unit identity. No flatness is required.
The calculation also applies to zero rings and zero complexes.
(blueprint: lem-fix-condensed-tensor-pullback-mate) -/
private theorem tensorScalarCompCounit
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
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
    rw [← cancel_mono ((Mod.comap (φ ≫ ψ)).mapDerivedCategoryFactorsh.hom.app M)]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [hn, ← hf]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
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
    | erw [Category.comp_id] at hUi
  repeat' first
    | erw [CategoryTheory.Functor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]
  erw [← reassoc_of% hUi]
  rfl




variable {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
  (a : A ⟶ B) [IsMonHom a]


private theorem derived_unique_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    {q : C ⥤ D} {F : C ⥤ E} (W : MorphismProperty C) [q.IsLocalization W]
    (LF LF' : D ⥤ E) (c : q ⋙ LF ⟶ F) (c' : q ⋙ LF' ⟶ F)
    [LF.IsLeftDerivedFunctor c W] [LF'.IsLeftDerivedFunctor c' W] (K : C) :
    (Functor.leftDerivedUnique LF' LF c c' W).hom.app (q.obj K) ≫ c'.app K = c.app K := by
  simpa only [Functor.leftDerivedUnique, Functor.leftDerivedNatIso_hom,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
    Functor.leftDerivedNatTrans_app LF LF' c c' W (𝟙 _) K

set_option maxHeartbeats 2000000 in
-- Comparing the internal module-object derived functors needs this elaboration budget.
set_option synthInstance.maxHeartbeats 200000 in
/-- The specified nonflat derived scalar pullback comparison has the specified restriction mate.

Source: the final associativity/counit compatibility paragraph of the latest blueprint's
`lem-fix-compact-support-coefficient-change`.

Proof in words. Apply the existing derived mate/counit theorem to the underived identity
`mateEquiv_pullIso_hom`. The scalar adjunction counits have the required normalization
on Qh. For the left comparison, expand the chosen construction of the derived scalar
pullback isomorphism. Derived natural-transformation counit compatibility handles its
underived comparison factor, and uniqueness of left derived functors handles its two
exact composition factors. Naturality moves scalar transitivity to the complex input.
Factor the underived comparison into scalar transitivity and pullIso, apply
`tensorScalarCompCounit`, and cancel transitivity with its inverse. The last factor is
the counit equation for `leftDerivedUpperStarIso`. This one-arrow calculation has no
properness, constructibility, or nonzero-ring hypothesis.
(blueprint: lem-fix-condensed-tensor-pullback-mate) -/
theorem tensorPullbackMateNormalization {U V : Scheme.{u}} (h : U ⟶ V) :
    mateEquiv (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a V))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))
      (TwoSquare.mk _ _ _ _ (derivedUpperStarExtendScalarsIso a h).hom) =
      (derivedComapLeftDerivedUpperStarIso a h).hom := by
  let β := (pullIso a h).symm
  let e := (comapUpperStarIso a h).symm
  let Lβ := (derivedUpperStarExtendScalarsIso a h).symm
  let Γ := derivedComapLeftDerivedUpperStarIso a h
  refine Adjunction.mateEquiv_leftDerived_inv_eq
    (Mod.extendRestrictAdjunction (coefficientMap a V))
    (Mod.extendRestrictAdjunction (coefficientMap a U)) β e
    (mateEquiv_pullIso_hom a h)
    (Functor.mapHomotopyCategoryCompNatIso (pullIso a h) _).symm
    (Functor.mapHomotopyCategoryCompNatIso_hom (pullIso a h) _)
    _ _ _ _
    ((h)^*⟦A⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac)
    _ _ ((h)^*⟦B⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a V))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))
    (Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh_eq _)
    (Mod.derivedExtendMapDerivedCategoryAdjunction_counit_app_Qh_eq _)
    Lβ _ rfl _ rfl (fun K => ?_) Γ (by rfl)
  simp only [Lβ, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.mapHomotopyCategoryCompNatIso_hom,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc]
  simp only [derivedUpperStarExtendScalarsIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Category.id_comp, Category.assoc]
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory B h).inv.naturality
    ((Mod.extendScalars (coefficientMap a V)).leftDerivedFunctorCounit.app K)
  simp only [Functor.comp_obj] at hn
  rw [← reassoc_of% hn]
  have hB := (h)^*⟦B⟧.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac
    (((Mod.extendScalars (coefficientMap a V)).mapHomotopyCategory (.up ℤ)).obj K)
  rw [← hB]
  simp only [leftDerivedUpperStarIsoMapDerivedCategory, Iso.inv_hom_id_app_assoc]
  have hr := derived_unique_fac
    (HomotopyCategory.quasiIso _ (.up ℤ))
    L(Mod.extendScalars (coefficientMap a V) ⋙ (h)^*⟦B⟧)
    (L(Mod.extendScalars (coefficientMap a V)) ⋙ D((h)^*⟦B⟧))
    (Mod.extendScalars (coefficientMap a V) ⋙ (h)^*⟦B⟧).leftDerivedFunctorCounit
    (Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit _ _) K
  change (Functor.leftDerivedFunctorCompMapDerivedCategoryRightIso
      (Mod.extendScalars (coefficientMap a V)) (h)^*⟦B⟧).hom.app
        (DerivedCategory.Qh.obj K) ≫
      (Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit _ _).app K = _ at hr
  simp only [Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Category.id_comp] at hr
  dsimp only [Functor.comp_obj] at hr
  change _ ≫ _ ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _) = _ at hr
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hr
  erw [hr]
  have hi := Functor.leftDerivedNatTrans_app
    L((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V) ⋙
      Mod.extendScalars (condensedPullbackHom A h ≫ coefficientMap a U))
    L(Mod.extendScalars (coefficientMap a V) ⋙ (h)^*⟦B⟧)
    ((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V) ⋙
      Mod.extendScalars (condensedPullbackHom A h ≫ coefficientMap a U)).leftDerivedFunctorCounit
    (Mod.extendScalars (coefficientMap a V) ⋙ (h)^*⟦B⟧).leftDerivedFunctorCounit
    (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (mapModUpperStarExtendScalarsIso a h).hom (.up ℤ))
      DerivedCategory.Qh) K
  change (Functor.leftDerivedFunctorIsoOfIso (mapModUpperStarExtendScalarsIso a h)).hom.app
      (DerivedCategory.Qh.obj K) ≫ _ = _ at hi
  simp only [Functor.whiskerRight_app] at hi
  erw [hi]
  have := Functor.isLeftDerivedFunctor_mapDerivedCategory_comp_leftDerivedFunctor
    ((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V))
    (Mod.extendScalars (condensedPullbackHom A h ≫ coefficientMap a U))
  have hl := derived_unique_fac (HomotopyCategory.quasiIso _ (.up ℤ))
    L((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V) ⋙
      Mod.extendScalars (condensedPullbackHom A h ≫ coefficientMap a U))
    (D((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V)) ⋙
      L(Mod.extendScalars (condensedPullbackHom A h ≫ coefficientMap a U)))
    ((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V) ⋙
      Mod.extendScalars (condensedPullbackHom A h ≫ coefficientMap a U)).leftDerivedFunctorCounit
    (Functor.leftDerivedFunctorCompMapDerivedCategoryCounit _ _) K
  change (Functor.leftDerivedFunctorCompMapDerivedCategoryIso _ _).hom.app
    (DerivedCategory.Qh.obj K) ≫ _ = _ at hl
  rw [← hl]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [Functor.leftDerivedFunctorCompMapDerivedCategoryCounit,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp, Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have ht := (Mod.derivedExtendScalarsCompIso (condensedPullbackHom A h)
    (coefficientMap a U) _ rfl).inv.naturality
      (((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V)).mapDerivedCategoryFactorsh.hom.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at ht
  rw [← reassoc_of% ht]
  have hm : (NatTrans.mapHomotopyCategory
      (mapModUpperStarExtendScalarsIso a h).hom (.up ℤ)).app K =
      (NatTrans.mapHomotopyCategory
        (Mod.extendScalarsComp (condensedPullbackHom A h) (coefficientMap a U)).hom
        (.up ℤ)).app
          ((((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V)).mapHomotopyCategory
            (.up ℤ)).obj K) ≫
        (NatTrans.mapHomotopyCategory (pullIso a h).hom (.up ℤ)).app K := by
    obtain ⟨C, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    change (HomotopyCategory.quotient _ (.up ℤ)).map _ =
      (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient _ (.up ℤ)).map _
    rw [← Functor.map_comp]
    congr 1
  rw [hm, Functor.map_comp]
  have hs := tensorScalarCompCounit (condensedPullbackHom A h) (coefficientMap a U)
    ((((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V)).mapHomotopyCategory (.up ℤ)).obj K)
  simp only [Functor.mapHomotopyCategoryCompIso_refl_inv_app, Category.comp_id] at hs
  have hs' := congrArg (fun m =>
    (Mod.derivedExtendScalarsCompIso (condensedPullbackHom A h)
      (coefficientMap a U) _ rfl).inv.app
        (DerivedCategory.Qh.obj
          ((((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V)).mapHomotopyCategory
            (.up ℤ)).obj K)) ≫ m) hs
  simp only [Iso.inv_hom_id_app_assoc] at hs'
  rw [← reassoc_of% hs']
  have := Functor.isLeftDerivedFunctor_mapDerivedCategory_comp_leftDerivedFunctor
    ((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V))
    (Mod.extendScalars (condensedPullbackHom A h))
  have hA := derived_unique_fac (HomotopyCategory.quasiIso _ (.up ℤ))
    L((h)^*⟦A⟧)
    (D((h)^*[Ab.{u + 1}].mapMod (condensedRingObj A V)) ⋙
      L(Mod.extendScalars (condensedPullbackHom A h)))
    (h)^*⟦A⟧.leftDerivedFunctorCounit
    (Functor.leftDerivedFunctorCompMapDerivedCategoryCounit _ _) K
  change (leftDerivedUpperStarIso A h).hom.app (DerivedCategory.Qh.obj K) ≫ _ = _ at hA
  simp only [Functor.leftDerivedFunctorCompMapDerivedCategoryCounit,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at hA
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hA
  simp only [← Functor.map_comp_assoc]
  erw [hA]
  rfl



end AlgebraicGeometry.ProEtale.CondensedRing
