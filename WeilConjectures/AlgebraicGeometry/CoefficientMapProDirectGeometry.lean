/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeCoefficientExtensionData
import WeilConjectures.AlgebraicGeometry.ProScalarPullNormalization
import all WeilConjectures.AlgebraicGeometry.FiniteCoefficientDirectImage

/-! # Geometric naturality of the pro-etale direct-image coefficient comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients



private def scalarMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Y X : Scheme.{u}} (f : Y ⟶ X) :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (TwoSquare.mk _ _ _ _ (Sites.proScalarPull φ f).hom)).natTrans

private theorem pro_derived_coefficient_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X' X Y' Y : Scheme.{u}}
    (h : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : CommSq h f' f g) (N : Sites.D true A Y) :
    (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} B) sq).hom.app
        ((Sites.scalar true φ Y).obj N) ≫
      (Sites.proPull B h).map ((Sites.proScalarPull φ f).hom.app N) ≫
      (Sites.proScalarPull φ h).hom.app ((Sites.proPull A f).obj N) =
    (Sites.proPull B f').map ((Sites.proScalarPull φ g).hom.app N) ≫
      (Sites.proScalarPull φ f').hom.app ((Sites.proPull A g).obj N) ≫
      (Sites.scalar true φ X').map
        ((leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} A) sq).hom.app N) := by
  have hh := pro_scalarPullback_composition φ f h N
  have hg := pro_scalarPullback_composition φ g f' N
  have hc {p q : X' ⟶ Y} (w : p = q) :
      (leftDerivedUpperStarCongr (ModuleCat.{u + 1} B) w).hom.app
          ((Sites.scalar true φ Y).obj N) ≫ (Sites.proScalarPull φ q).hom.app N =
        (Sites.proScalarPull φ p).hom.app N ≫
          (Sites.scalar true φ X').map
            ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) w).hom.app N) := by
    subst q
    simp only [leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app,
      Functor.comp_obj, Category.id_comp]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  apply (cancel_epi
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} B) f' g).hom.app
      ((Sites.scalar true φ Y).obj N))).mp
  simp only [leftDerivedUpperStarSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [hh, reassoc_of% hc sq.w.symm, reassoc_of% hg]
  simp only [← Functor.map_comp, ← Category.assoc, Iso.hom_inv_id_app]
  simp only [Functor.comp_obj]
  erw [Category.id_comp]

private theorem pro_derived_coefficient_exchange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X' X Y' Y : Scheme.{u}}
    (h : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : ChosenCartesianSquare h f' f g) (M : Sites.D true A X) :
    L(upperStar (ModuleCat.{u + 1} B) g).map ((scalarMate φ f).app M) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq).app
          ((Sites.scalar true φ X).obj M) ≫
        R(lowerStar (ModuleCat.{u + 1} B) f').map
          ((Sites.proScalarPull φ h).hom.app M) =
      (Sites.proScalarPull φ g).hom.app
          (R(lowerStar (ModuleCat.{u + 1} A) f).obj M) ≫
        (Sites.scalar true φ Y').map
          ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app M) ≫
        (scalarMate φ f').app (L(upperStar (ModuleCat.{u + 1} A) h).obj M) := by
  let PA {S T : Scheme.{u}} (v : S ⟶ T) := Sites.proPull A v
  let PB {S T : Scheme.{u}} (v : S ⟶ T) := Sites.proPull B v
  let QA (T : Scheme.{u}) := Sites.scalar true φ T
  let afA := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let afB := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f
  let afA' := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f'
  let afB' := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f'
  let θA := leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} A) sq.toCommSq
  let θB := leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} B) sq.toCommSq
  let lp {S T : Scheme.{u}} (v : S ⟶ T) := (Sites.proScalarPull φ v).hom
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
    (TwoSquare.mk _ _ _ _ (Sites.proScalarPull φ f).hom) M
  have hf' := mateEquiv_counit afA' afB'
    (TwoSquare.mk _ _ _ _ (Sites.proScalarPull φ f').hom) ((PA h).obj M)
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
  change (PB f').map (R(lowerStar (ModuleCat.{u + 1} B) f').map ((lp h).app M)) ≫
      afB'.counit.app ((QA X').obj ((PA h).obj M)) =
    afB'.counit.app ((PB h).obj ((QA X).obj M)) ≫ (lp h).app M at nc
  change (PB f').map ((PB g).map ((scalarMate φ f).app M)) ≫
      θB.hom.app (R(lowerStar (ModuleCat.{u + 1} B) f).obj ((QA X).obj M)) =
    θB.hom.app ((QA Y).obj (R(lowerStar (ModuleCat.{u + 1} A) f).obj M)) ≫
      (PB h).map ((PB f).map ((scalarMate φ f).app M)) at ns
  change (PB h).map ((QA X).map (afA.counit.app M)) ≫ (lp h).app M =
    (lp h).app ((PA f).obj (R(lowerStar (ModuleCat.{u + 1} A) f).obj M)) ≫
      (QA X').map ((PA h).map (afA.counit.app M)) at nh
  change (PB f').map ((QA Y').map (eA.app M)) ≫
      (lp f').app (R(lowerStar (ModuleCat.{u + 1} A) f').obj ((PA h).obj M)) =
    (lp f').app ((PA g).obj (R(lowerStar (ModuleCat.{u + 1} A) f).obj M)) ≫
      (QA X').map ((PA f').map (eA.app M)) at nf'
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
  rw [← (QA X').map_comp, heA, (QA X').map_comp]
  simpa only [PA, PB, QA, θA, θB, lp, Functor.map_comp, Category.assoc] using
    congrArg (fun t ↦ t ≫ (QA X').map ((PA h).map (afA.counit.app M)))
      (pro_derived_coefficient_square φ h f' f g sq.toCommSq
        (R(lowerStar (ModuleCat.{u + 1} A) f).obj M))


/-- The pro-etale coefficient direct-image map respects geometric isomorphisms.
Source: blueprint latest, lem-coef-finite-free-extension.proof.md, final paragraph.
(blueprint: lem-sf-coefficient-map-pro-direct-geometry).
Proof: the restriction/pullback compositor gives the scalar/pullback square by
iterated mates. Transpose the desired direct-image square under the primed B
geometric adjunction. Its counit equation and naturality reduce it to this square,
postcomposed with the extended A-counit. Injectivity of transposition proves the
identity. Cancel the two scalar/pullback isomorphisms to get the stated orientation.
This works on all complexes, including the constructible finite-Tor domain. -/
theorem coefficient_map_pro_direct_geometry
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {T X : Scheme.{u}} (f : T ⟶ X) : Sites.ProDirectGeometry φ f := by
  intro Y e K _hK
  let sq : ChosenCartesianSquare (pullback.fst f e.hom) (pullback.snd f e.hom) f e.hom := {
    toCommSq := (IsPullback.of_hasPullback f e.hom).toCommSq
    isoPullback := Iso.refl _
    hom_fst := Category.id_comp _
    hom_snd := Category.id_comp _ }
  have q := pro_derived_coefficient_exchange φ _ _ _ _ sq K
  have q' := congrArg (fun z ↦
    (Sites.proScalarPull φ e.hom).inv.app ((R(lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫
      z ≫ (R(lowerStar (ModuleCat.{u + 1} B) (pullback.snd f e.hom))).map
        ((Sites.proScalarPull φ (pullback.fst f e.hom)).inv.app K)) q
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app] at q'
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at q'
  simpa only [ProEtale.finiteCoefficientDirectImageMap_eq_mate, scalarMate,
    proScalarPull_eq_scalarPullbackProEtaleIso, Sites.proPull, Sites.scalar, id_eq,
    Functor.comp_obj] using q'.symm

end WeilConjectures.FiniteFreeCoefficients
