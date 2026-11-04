/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Support.SupportScalarProjectionCoordinates
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Open.OpenScalarCounitSquare
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
import WeilConjectures.SmoothPurity.Support.SupportScalarMateAux
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Comma.Arrow
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
/-- Canonical support mate factors through the invertible open scalar mate.
Source: Stacks 03DI, 0GL6 and 07A6; (blueprint: lem-exc-support-scalar-open-transport).
(blueprint: new-support-scalar-mate-canonical-open).
Proof: expand `sfCompactSupportRestriction`, apply `mateEquiv_vcomp`, so the mate is the
direct-image mate followed by the open mate. The open mate is invertible: its iterated mate
along the derived extension-by-zero adjunctions (whose units are invertible) is built from
those units, the open scalar square and the open restriction square. Remove it by
`Arrow.isoMk` and naturality of the direct-image mate. -/
theorem supportScalarMate_canonical_open
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (LY : proEtaleDerivedCategory Y A ⥤ proEtaleDerivedCategory Y B)
    (aY : LY ⊣ (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory)
    (K : DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Nonempty (Arrow.mk
      (((proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Y A).inverse).map
        (((mateEquiv
          (Scheme.proEtaleRingDerivedExtensionAdjunction
            (proEtaleConstantRingMap (T := X) φ))
          aY).symm
          (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom)).natTrans.app
          ((sfIntrinsicDerivedEquivalence X A).functor.obj K))) ≅
      properScalarMateArrow φ c.g
        (AlgebraicGeometry.ProEtale.scalarExtension φ c.Z)
        LY
        (Scheme.proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := c.Z) φ))
        aY
        ((ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory.obj K)) := by
  classical
  let aX := Scheme.proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) φ)
  let aZ := Scheme.proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := c.Z) φ)
  let sq₁ := Functor.mapDerivedCategorySquareIso (sfOpenRestriction c.i φ)
  let α := TwoSquare.mk _ _ _ _ sq₁.hom
  let β := TwoSquare.mk _ _ _ _ (sfDerivedImageRestriction c.g φ).hom
  have hsplit :
      TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom = TwoSquare.vComp α β := by
    ext E
    simp only [Functor.comp_obj, TwoSquare.vComp_app]
    simp [sfCompactSupportRestriction, α, β, sq₁]
  let m₁ := (mateEquiv aX aZ).symm α
  let m₂ := (mateEquiv aZ aY).symm β
  have hm : (mateEquiv aX aY).symm
      (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom) =
        TwoSquare.hComp m₁ m₂ := by
    rw [hsplit]
    exact mateEquiv_symm_vComp aX aZ aY α β
  have hiso : IsIso m₁.natTrans :=
    mateEquiv_symm_isIso_of_unit_isIso aX aZ (sfIntrinsicDerivedOpenAdjunction c.i A)
      (sfIntrinsicDerivedOpenAdjunction c.i B) sq₁
      (Functor.mapDerivedCategorySquareIso (sfOpenRestrictionCoefficientSquare c.i φ))
  let eX := sfIntrinsicModuleEquivalence X A
  let eZ := sfIntrinsicModuleEquivalence c.Z A
  let LS := ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i
  let E := (sfIntrinsicDerivedEquivalence X A).functor.obj K
  let ι : (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory.obj E ≅
      (sfIntrinsicDerivedEquivalence c.Z A).functor.obj (LS.mapDerivedCategory.obj K) :=
    (Functor.mapDerivedCategoryCompIso eX.inverse (LS ⋙ eZ.functor)).app E ≪≫
      (LS ⋙ eZ.functor).mapDerivedCategory.mapIso
        ((eX.mapDerivedCategory.unitIso.app K).symm) ≪≫
      (Functor.mapDerivedCategoryCompIso LS eZ.functor).app K
  let F := (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence Y A).inverse
  let Rg := proEtaleConstantDerivedDirectImage c.g B
  refine ⟨Arrow.isoMk
    (F.mapIso (LY.mapIso ((proEtaleConstantDerivedDirectImage c.g A).mapIso ι)))
    (F.mapIso (Rg.mapIso ((asIso (m₁.natTrans.app E)).symm ≪≫
      (ProEtale.scalarExtension φ c.Z).mapIso ι))) ?_⟩
  have hc := congrArg (fun w ↦ w.natTrans.app E) hm
  simp only [TwoSquare.hComp_app] at hc
  have key : ((mateEquiv aX aY).symm
      (TwoSquare.mk _ _ _ _ (sfCompactSupportRestriction c φ).hom)).natTrans.app E ≫
        Rg.map (((asIso (m₁.natTrans.app E)).symm ≪≫
          (ProEtale.scalarExtension φ c.Z).mapIso ι).hom) =
      LY.map ((proEtaleConstantDerivedDirectImage c.g A).map ι.hom) ≫
        m₂.natTrans.app
          ((sfIntrinsicDerivedEquivalence c.Z A).functor.obj (LS.mapDerivedCategory.obj K)) := by
    refine (congrArg (· ≫ _) hc).trans ?_
    rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, ← Rg.map_comp,
      IsIso.hom_inv_id_assoc]
    exact (m₂.natTrans.naturality ι.hom).symm
  exact (F.map_comp _ _).symm.trans ((congrArg F.map key.symm).trans (F.map_comp _ _))
end WeilConjectures
