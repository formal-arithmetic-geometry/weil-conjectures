/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeCoefficientExtensionData
import all WeilConjectures.AlgebraicGeometry.FiniteCoefficientDirectImage
import all WeilConjectures.AlgebraicGeometry.EtaleScalarPullbackCompactification

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

private theorem derived_coefficient_exchange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X' X Y' Y : Scheme.{u}}
    (h : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : ChosenCartesianSquare h f' f g) (M : DerivedCategoryModule A X) :
    L(upperStar (ModuleCat.{u + 1} B) g).map ((scalarMate φ f).app M) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq).app
          ((scalarExtension φ X).obj M) ≫
        R(lowerStar (ModuleCat.{u + 1} B) f').map
          ((scalarPullbackIso φ h).hom.app M) =
      (scalarPullbackIso φ g).hom.app
          (R(lowerStar (ModuleCat.{u + 1} A) f).obj M) ≫
        (scalarExtension φ Y').map
          ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app M) ≫
        (scalarMate φ f').app (L(upperStar (ModuleCat.{u + 1} A) h).obj M) := by
  let PA {S T : Scheme.{u}} (v : S ⟶ T) := L(upperStar (ModuleCat.{u + 1} A) v)
  let PB {S T : Scheme.{u}} (v : S ⟶ T) := L(upperStar (ModuleCat.{u + 1} B) v)
  let QA (T : Scheme.{u}) := scalarExtension φ T
  let afA := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let afB := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let afA' := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f'
  let afB' := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f'
  let θA := derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq
  let θB := derivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq.toCommSq
  let lp {S T : Scheme.{u}} (v : S ⟶ T) := (scalarPullbackIso φ v).hom
  let eA := derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq
  let eB := derivedBaseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq
  have heA : (PA f').map (eA.app M) ≫ afA'.counit.app ((PA h).obj M) =
      θA.hom.app (R(lowerStar (ModuleCat.{u + 1} A) f).obj M) ≫
        (PA h).map (afA.counit.app M) :=
    mateEquiv_counit afA afA' (TwoSquare.mk _ _ _ _ θA.hom) M
  have heB : (PB f').map (eB.app ((QA X).obj M)) ≫
      afB'.counit.app ((PB h).obj ((QA X).obj M)) =
      θB.hom.app (R(lowerStar (ModuleCat.{u + 1} B) f).obj ((QA X).obj M)) ≫
        (PB h).map (afB.counit.app ((QA X).obj M)) :=
    mateEquiv_counit afB afB' (TwoSquare.mk _ _ _ _ θB.hom) ((QA X).obj M)
  have hf := mateEquiv_counit afA afB
    (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ f).hom) M
  have hf' := mateEquiv_counit afA' afB'
    (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ f').hom) ((PA h).obj M)
  change (PB f).map ((scalarMate φ f).app M) ≫
      afB.counit.app ((QA X).obj M) =
    (lp f).app (R(lowerStar (ModuleCat.{u + 1} A) f).obj M) ≫
      (QA X).map (afA.counit.app M) at hf
  change (PB f').map ((scalarMate φ f').app ((PA h).obj M)) ≫
      afB'.counit.app ((QA X').obj ((PA h).obj M)) =
    (lp f').app (R(lowerStar (ModuleCat.{u + 1} A) f').obj ((PA h).obj M)) ≫
      (QA X').map (afA'.counit.app ((PA h).obj M)) at hf'
  have nc := afB'.counit.naturality ((lp h).app M)
  have ns := θB.hom.naturality ((scalarMate φ f).app M)
  have nh := (lp h).naturality (afA.counit.app M)
  have nf' := (lp f').naturality (eA.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at nc ns nh nf'
  apply (afB'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  change (PB f').map ((PB g).map ((scalarMate φ f).app M)) ≫
      (PB f').map (eB.app ((QA X).obj M)) ≫
      (PB f').map (R(lowerStar (ModuleCat.{u + 1} B) f').map ((lp h).app M)) ≫
      afB'.counit.app ((QA X').obj ((PA h).obj M)) =
    (PB f').map ((lp g).app (R(lowerStar (ModuleCat.{u + 1} A) f).obj M)) ≫
      (PB f').map ((QA Y').map (eA.app M)) ≫
      (PB f').map ((scalarMate φ f').app ((PA h).obj M)) ≫
      afB'.counit.app ((QA X').obj ((PA h).obj M))
  rw [nc, reassoc_of% heB, reassoc_of% ns]
  rw [← Functor.map_comp_assoc, hf, Functor.map_comp]
  simp only [Category.assoc]
  rw [nh, hf', reassoc_of% nf']
  rw [← Functor.map_comp, heA, Functor.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun t ↦ t ≫ (QA X').map ((PA h).map (afA.counit.app M)))
      (derived_coefficient_square φ h f' f g sq.toCommSq
        (R(lowerStar (ModuleCat.{u + 1} A) f).obj M))


/-- The coefficient direct-image comparison respects isomorphism base change on
all derived objects, without flatness of the coefficient map.
Source: blueprint latest, lem-coef-finite-free-extension.proof.md, final paragraph.
(blueprint: lem-sf-coefficient-map-direct-geometry).
Proof: transport scalar/pullback composition through the exact/left-derived
comparison. Cancel the comparison at the common composite to obtain its square.
Transpose the direct-image square under the primed B geometric adjunction. The
mate/counit equations and counit naturality identify both transposes with the
scalar/pullback square followed by the image of the A-counit. Injectivity of the
Hom equivalence proves equality; cancel scalar/pullback inverses for the stated
orientation. The argument does not need a constructibility assumption. -/
theorem coefficient_map_direct_geometry
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {T X : Scheme.{u}} (f : T ⟶ X)
    (Y : Scheme.{u}) (e : Y ≅ X) (K : Cat A T) :
    (Etale.scalarExtension φ Y).map
        ((Etale.derivedBaseChangeMap (ModuleCat.{u + 1} A)
          (IsPullback.of_hasPullback f e.hom).toCommSq).app K) ≫
      Etale.finiteCoefficientDirectImageMap φ (pullback.snd f e.hom)
        ((Sites.pull A (pullback.fst f e.hom)).obj K) ≫
      (R(Etale.lowerStar (ModuleCat.{u + 1} B) (pullback.snd f e.hom))).map
        ((Etale.scalarPullbackIso φ (pullback.fst f e.hom)).inv.app K) =
    (Sites.scalarPull φ e.hom).inv.app
        ((R(Etale.lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫
      (Sites.pull B e.hom).map (Etale.finiteCoefficientDirectImageMap φ f K) ≫
      (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} B)
        (IsPullback.of_hasPullback f e.hom).toCommSq).app ((Etale.scalarExtension φ T).obj K) := by
  let sq : ChosenCartesianSquare (pullback.fst f e.hom) (pullback.snd f e.hom) f e.hom := {
    toCommSq := (IsPullback.of_hasPullback f e.hom).toCommSq
    isoPullback := Iso.refl _
    hom_fst := Category.id_comp _
    hom_snd := Category.id_comp _ }
  have q := derived_coefficient_exchange φ _ _ _ _ sq K
  have q' := congrArg (fun z ↦
    (scalarPullbackIso φ e.hom).inv.app ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫
      z ≫ (R(lowerStar (ModuleCat.{u + 1} B) (pullback.snd f e.hom))).map
        ((scalarPullbackIso φ (pullback.fst f e.hom)).inv.app K)) q
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app] at q'
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at q'
  simpa only [Etale.finiteCoefficientDirectImageMap_eq_mate, scalarMate,
    ProEtale.scalarPullbackEtaleIso, Sites.scalarPull, Sites.pull] using q'.symm

end WeilConjectures.FiniteFreeCoefficients
