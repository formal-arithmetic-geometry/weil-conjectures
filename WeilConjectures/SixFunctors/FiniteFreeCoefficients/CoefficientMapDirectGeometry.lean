/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import all WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackCompactification

/-! # Geometric naturality of the ordinary direct-image coefficient comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

private theorem scalar_derived_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X T₁ T₂ : Scheme.{u}}
    (v : T₁ ⟶ T₂) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (h : j₁ ≫ v = j₂)
    (N : Cat A T₂) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} B) j₁ v j₂ h.symm).hom.app
        ((Etale.scalarExtension φ T₂).obj N) ≫
      (Sites.pull B j₁).map ((Etale.scalarPullbackIso φ v).hom.app N) ≫
      (Etale.scalarPullbackIso φ j₁).hom.app ((Sites.pull A v).obj N) =
    (Etale.scalarPullbackIso φ j₂).hom.app N ≫
      (Etale.scalarExtension φ X).map
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j₁ v j₂ h.symm).hom.app N) := by
  let eA := fun {V W : Scheme.{u}} (p : V ⟶ W) ↦
    leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p
  let eB := fun {V W : Scheme.{u}} (p : V ⟶ W) ↦
    leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) p
  let cA := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) j₁ v j₂ h.symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  let cB := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} B) j₁ v j₂ h.symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  have q := scalarPullback_composition φ v j₁ j₂ h N
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] at q
  have ht := transport_composition (scalarExtension φ T₂) (scalarExtension φ T₁)
    (scalarExtension φ X) (eA v) (eA j₁) (eA j₂) (eB v) (eB j₁) (eB j₂)
    (scalarPullbackIso φ v) (scalarPullbackIso φ j₁) (scalarPullbackIso φ j₂)
    cA cB N (by
      simpa only [eA, eB, cA, cB, Iso.trans_hom, NatTrans.comp_app,
        Functor.map_comp, Category.assoc] using q)
  simpa only [Sites.pull, leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
    eA, eB, cA, cB, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc] using ht

private theorem derived_coefficient_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X' X Y' Y : Scheme.{u}}
    (h : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : CommSq h f' f g) (N : Cat A Y) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq).hom.app
        ((scalarExtension φ Y).obj N) ≫
      L(upperStar (ModuleCat.{u + 1} B) h).map
        ((scalarPullbackIso φ f).hom.app N) ≫
      (scalarPullbackIso φ h).hom.app
        (L(upperStar (ModuleCat.{u + 1} A) f).obj N) =
    L(upperStar (ModuleCat.{u + 1} B) f').map
        ((scalarPullbackIso φ g).hom.app N) ≫
      (scalarPullbackIso φ f').hom.app
        (L(upperStar (ModuleCat.{u + 1} A) g).obj N) ≫
      (scalarExtension φ X').map
        ((derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app N) := by
  have hh := scalar_derived_composition φ f h (h ≫ f) rfl N
  have hg := scalar_derived_composition φ g f' (h ≫ f) sq.w.symm N
  let ch (R : Type (u + 1)) [CommRing R] :=
    leftDerivedUpperStarComp (ModuleCat.{u + 1} R) h f
  let cg (R : Type (u + 1)) [CommRing R] :=
    leftDerivedUpperStarComp (ModuleCat.{u + 1} R) f' g (h ≫ f) sq.w
  have hs (R : Type (u + 1)) [CommRing R] :
      (derivedSquareUpperStarIso (ModuleCat.{u + 1} R) sq).hom =
        (cg R).inv ≫ (ch R).hom := rfl
  apply (cancel_epi ((cg B).hom.app ((scalarExtension φ Y).obj N))).mp
  simp only [hs, NatTrans.comp_app, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp]
  simp only [Category.assoc]
  dsimp only [ch, cg]
  simp only [Sites.pull] at hh hg
  rw [hh, reassoc_of% hg]
  simp only [← Functor.map_comp, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp]

end WeilConjectures.FiniteFreeCoefficients
