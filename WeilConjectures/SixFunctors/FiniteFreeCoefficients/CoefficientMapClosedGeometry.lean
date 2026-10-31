/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import all WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapDirectGeometry
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.CategoryTheory.SixFunctors.PointwiseExchangeMateCube
import WeilConjectures.SixFunctors.Etale.Derived.WeilOperations

/-! # Scheme-isomorphism naturality for the closed coefficient counit mate -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients



private theorem inverseOnDomain_equivalence_square
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.ReflectsIsomorphisms]
    {X Y : C} {X' Y' : D} (f : X ⟶ Y) (g : X' ⟶ Y')
    (a : F.obj X ≅ X') (b : F.obj Y ≅ Y')
    (h : F.map f ≫ b.hom = a.hom ≫ g) :
    F.map (Sites.inverseOnDomain f) ≫ a.hom =
      b.hom ≫ Sites.inverseOnDomain g := by
  classical
  have hg : g = a.inv ≫ F.map f ≫ b.hom := by
    rw [h, Iso.inv_hom_id_assoc]
  have hf : F.map f = a.hom ≫ g ≫ b.inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  by_cases hi : IsIso f
  · have := hi
    have : IsIso g := by rw [hg]; infer_instance
    simp only [Sites.inverseOnDomain, dif_pos hi, dif_pos (inferInstance : IsIso g)]
    apply (cancel_epi (F.map f)).mp
    simp only [← F.map_comp_assoc, IsIso.hom_inv_id, F.map_id, Category.id_comp]
    rw [reassoc_of% h, IsIso.hom_inv_id, Category.comp_id]
  · have hn : ¬ IsIso g := by
      intro hi'
      have := hi'
      have : IsIso (F.map f) := by rw [hf]; infer_instance
      exact hi (isIso_of_reflects_iso f F)
    simp only [Sites.inverseOnDomain, dif_neg hi, dif_neg hn,
      F.map_zero, zero_comp, comp_zero]

local instance pull_additive (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) : (Sites.pull A g).Additive := by
  dsimp only [Sites.pull]
  infer_instance

local instance pull_equivalence (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) [IsIso g] : (Sites.pull A g).IsEquivalence := by
  dsimp only [Sites.pull]
  infer_instance

private def coefficientInv
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) (N : Cat A Z) :=
  Sites.inverseOnDomain (finiteCoefficientDirectImageMap φ i N)

private theorem coefficientInv_naturality_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X)
    {N M : Cat A Z} (f : N ⟶ M) (hf : IsIso f) :
    R(lowerStar (ModuleCat.{u + 1} B) i).map ((scalarExtension φ Z).map f) ≫
        coefficientInv φ i M =
      coefficientInv φ i N ≫
        (scalarExtension φ X).map (R(lowerStar (ModuleCat.{u + 1} A) i).map f) := by
  have := hf
  let a := (scalarExtension φ X).mapIso
    ((R(lowerStar (ModuleCat.{u + 1} A) i)).mapIso (asIso f))
  let b := (R(lowerStar (ModuleCat.{u + 1} B) i)).mapIso
    ((scalarExtension φ Z).mapIso (asIso f))
  exact (inverseOnDomain_equivalence_square (𝟭 _)
    (finiteCoefficientDirectImageMap φ i N) (finiteCoefficientDirectImageMap φ i M)
    a b (finiteCoefficientDirectImageMap_naturality φ i f).symm).symm

private theorem closed_inverse_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (e : Y ≅ X)
    (exA : R(lowerStar (ModuleCat.{u + 1} A) i) ⋙ Sites.pull A e.hom ≅
      Sites.pull A (pullback.fst i e.hom) ⋙
        R(lowerStar (ModuleCat.{u + 1} A) (pullback.snd i e.hom)))
    (exB : R(lowerStar (ModuleCat.{u + 1} B) i) ⋙ Sites.pull B e.hom ≅
      Sites.pull B (pullback.fst i e.hom) ⋙
        R(lowerStar (ModuleCat.{u + 1} B) (pullback.snd i e.hom)))
    (hA : exA.hom = derivedBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback i e.hom).toCommSq)
    (hB : exB.hom = derivedBaseChangeMap (ModuleCat.{u + 1} B)
      (IsPullback.of_hasPullback i e.hom).toCommSq) (N : Cat A Z) :
    R(lowerStar (ModuleCat.{u + 1} B) (pullback.snd i e.hom)).map
        ((Sites.scalarPull φ (pullback.fst i e.hom)).inv.app N) ≫
      exB.inv.app ((scalarExtension φ Z).obj N) ≫
      (Sites.pull B e.hom).map (coefficientInv φ i N) =
    coefficientInv φ (pullback.snd i e.hom)
        ((Sites.pull A (pullback.fst i e.hom)).obj N) ≫
      (scalarExtension φ Y).map (exA.inv.app N) ≫
      (Sites.scalarPull φ e.hom).inv.app
        (R(lowerStar (ModuleCat.{u + 1} A) i).obj N) := by
  let RA := R(lowerStar (ModuleCat.{u + 1} A) i)
  let RB' := R(lowerStar (ModuleCat.{u + 1} B) (pullback.snd i e.hom))
  let Q := scalarExtension φ Y
  let lg := Sites.scalarPull φ e.hom
  let lh := Sites.scalarPull φ (pullback.fst i e.hom)
  let a := lg.app (RA.obj N) ≪≫ Q.mapIso (exA.app N)
  let b := exB.app ((scalarExtension φ Z).obj N) ≪≫ RB'.mapIso (lh.app N)
  have hs : (Sites.pull B e.hom).map (finiteCoefficientDirectImageMap φ i N) ≫
        b.hom = a.hom ≫ finiteCoefficientDirectImageMap φ (pullback.snd i e.hom)
          ((Sites.pull A (pullback.fst i e.hom)).obj N) := by
    let sq : ChosenCartesianSquare (pullback.fst i e.hom)
        (pullback.snd i e.hom) i e.hom := {
      toCommSq := (IsPullback.of_hasPullback i e.hom).toCommSq
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
    have q := derived_coefficient_exchange φ _ _ _ _ sq N
    simpa only [a, b, lg, lh, RA, RB', Q, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, hA, hB, Sites.scalarPull, Sites.pull,
      finiteCoefficientDirectImageMap_eq_mate, scalarMate,
      ProEtale.scalarPullbackEtaleIso, Category.assoc] using q
  have q := inverseOnDomain_equivalence_square (Sites.pull B e.hom)
    (finiteCoefficientDirectImageMap φ i N)
    (finiteCoefficientDirectImageMap φ (pullback.snd i e.hom)
      ((Sites.pull A (pullback.fst i e.hom)).obj N)) a b hs
  have q' := congrArg (fun z ↦ RB'.map (lh.inv.app N) ≫
    exB.inv.app ((scalarExtension φ Z).obj N) ≫ z ≫
      Q.map (exA.inv.app N) ≫ lg.inv.app (RA.obj N)) q
  simp only [a, b, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Functor.comp_obj, Category.id_comp] at q'
  simpa only [coefficientInv, RA, RB', Q, lg, lh, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app, Category.comp_id] using q'

/-- The actual closed right-adjoint coefficient comparison respects isomorphism pullback.
Source: blueprint latest, lem-coef-finite-free-extension.proof.md, final paragraph.
(blueprint: lem-sf-coefficient-map-closed-geometry).
Proof: direct-image base change along an isomorphism is invertible. Its coefficient
square conjugates the two coefficient direct-image arrows under the geometric
equivalence. Thus their inverse-or-zero extensions satisfy the inverse square,
including when neither is invertible. These pointwise inverses are natural along
isomorphisms, in particular along the closed geometric mate. Apply the pointwise
exchange mate cube to the four actual closed adjunctions. Cancel scalar/geometric
isomorphisms to obtain the asserted orientation. All counits are the specified
closed direct-image/right-adjoint counits. -/
theorem coefficient_map_closed_geometry
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∀ (Y : Scheme.{u}) (e : Y ≅ X) (M : Cat A X),
    (scalarExtension φ (pullback i e.hom)).map (Sites.closedPull A i e.hom M) ≫
      closedMap φ (pullback.snd i e.hom) ((Sites.pull A e.hom).obj M) ≫
      (closedUpper B (pullback.snd i e.hom)).map
        ((Sites.scalarPull φ e.hom).inv.app M) =
    (Sites.scalarPull φ (pullback.fst i e.hom)).inv.app ((closedUpper A i).obj M) ≫
      (Sites.pull B (pullback.fst i e.hom)).map (closedMap φ i M) ≫
      Sites.closedPull B i e.hom ((scalarExtension φ X).obj M) := by
  intro Y e M
  let h := pullback.fst i e.hom
  let j := pullback.snd i e.hom
  let sq := (IsPullback.of_hasPullback i e.hom).toCommSq
  have := isIso_derivedBaseChangeMap_of_isIso A sq
  have := isIso_derivedBaseChangeMap_of_isIso B sq
  let exA := asIso (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq)
  let exB := asIso (derivedBaseChangeMap (ModuleCat.{u + 1} B) sq)
  let a := Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i))
  let b := Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} B) i))
  let a' := Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) j))
  let b' := Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} B) j))
  have : IsIso (mateEquiv a a' (TwoSquare.mk _ _ _ _ exA.inv)).natTrans :=
    isIso_mateEquiv_of_isEquivalence a a' _
  have q := pointwiseExchangeMate_cube a b a' b'
    (Sites.pull A h) (Sites.pull A e.hom) (Sites.pull B h) (Sites.pull B e.hom)
    exA (Sites.scalarPull φ h) (Sites.scalarPull φ e.hom) exB
    (coefficientInv φ i) (coefficientInv φ j)
    (closed_inverse_cube φ i e exA exB rfl rfl)
    (fun f hf ↦ coefficientInv_naturality_iso φ j f hf) M (inferInstance)
  have q' := congrArg (fun z ↦
    (Sites.scalarPull φ h).inv.app ((closedUpper A i).obj M) ≫ z ≫
      (closedUpper B j).map ((Sites.scalarPull φ e.hom).inv.app M)) q
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app] at q'
  have hpa (N : Cat A Z) : Sites.inverseOnDomain
      ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app N) = exA.inv.app N := by
    simp only [Sites.inverseOnDomain, dif_pos (inferInstance : IsIso
      ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app N))]
    simp only [exA, asIso_inv, NatIso.isIso_inv_app]
  have hpb (N : Cat B Z) : Sites.inverseOnDomain
      ((derivedBaseChangeMap (ModuleCat.{u + 1} B) sq).app N) = exB.inv.app N := by
    simp only [Sites.inverseOnDomain, dif_pos (inferInstance : IsIso
      ((derivedBaseChangeMap (ModuleCat.{u + 1} B) sq).app N))]
    simp only [exB, asIso_inv, NatIso.isIso_inv_app]
  unfold Sites.closedPull
  erw [hpa, hpb]
  simpa only [closedMap, coefficientInv,
    Sites.inverseOnDomain, pointwiseExchangeMate, mate_app_eq_adjunct, a, b, a', b',
    Sites.scalar, id_eq, h, j, sq, Functor.comp_obj, Functor.id_obj,
    CategoryTheory.Functor.map_id, Category.comp_id] using q'.symm

end WeilConjectures.FiniteFreeCoefficients
