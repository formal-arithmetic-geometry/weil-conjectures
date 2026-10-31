/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import all WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientMapClosedGeometry
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.CoefficientSitePullCube
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.CategoryTheory.SixFunctors.PointwiseExchangeMateCube

/-! # The closed coefficient square under site-adjunction transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

local instance closed_site_pull_equivalence (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) [IsIso g] : (Sites.pull A g).IsEquivalence := by
  dsimp only [Sites.pull]
  infer_instance

local instance closed_site_proPull_equivalence (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) [IsIso g] : (Sites.proPull A g).IsEquivalence := by
  dsimp only [Sites.proPull]
  infer_instance

private theorem closed_coefficient_naturality_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {N M : Cat A X} (a : N ⟶ M) (ha : IsIso a) :
    (scalarExtension φ Z).map ((closedUpper A i).map a) ≫ closedMap φ i M =
      closedMap φ i N ≫ (closedUpper B i).map ((scalarExtension φ X).map a) := by
  exact pointwiseExchangeMate_naturality_iso
    (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i)))
    (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} B) i)))
    (coefficientInv φ i) (fun b hb ↦ coefficientInv_naturality_iso φ i b hb) a ha

private theorem closed_geometric_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (e : Y ≅ X)
    {N M : Cat A X} (a : N ⟶ M) :
    (Sites.pull A (pullback.fst i e.hom)).map ((closedUpper A i).map a) ≫
        Sites.closedPull A i e.hom M =
      Sites.closedPull A i e.hom N ≫
        (closedUpper A (pullback.snd i e.hom)).map ((Sites.pull A e.hom).map a) := by
  let sq := (IsPullback.of_hasPullback i e.hom).toCommSq
  have := isIso_derivedBaseChangeMap_of_isIso A sq
  let θ := (asIso (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq)).inv
  have h := (mateEquiv
    (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i)))
    (Adjunction.ofIsLeftAdjoint
      (R(lowerStar (ModuleCat.{u + 1} A) (pullback.snd i e.hom))))
    (TwoSquare.mk _ _ _ _ θ)).natTrans.naturality a
  have hi (L : Cat A Z) : Sites.inverseOnDomain
      ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app L) = θ.app L := by
    simp only [Sites.inverseOnDomain, dif_pos (inferInstance : IsIso
      ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app L)), θ,
      asIso_inv, NatIso.isIso_inv_app]
  unfold Sites.closedPull
  erw [hi, hi]
  simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj,
    mate_app_eq_adjunct, Sites.pull, closedUpper] using h

private theorem rnuPull_isIso
    (A : Type (u + 1)) [CommRing A] {Y X : Scheme.{u}} (e : Y ≅ X)
    (M : Sites.D true A X) : IsIso (Sites.rnuPull A e.hom M) := by
  let a := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X
  let b := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y
  let θ := (Sites.sitePull A e.hom).inv
  have : IsIso (mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).natTrans :=
    isIso_mateEquiv_of_isEquivalence a b _
  simpa only [mate_app_eq_adjunct, Sites.rnuPull, a, b, θ,
    Functor.comp_obj, Functor.id_obj, Sites.rnu] using
    (inferInstance : IsIso ((mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).app M))

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  closedMap Sites.closedPull Sites.rnuScalar Sites.rnuPull
  Sites.proScalarPull Sites.sitePull Sites.scalarSite Sites.scalarPull

private theorem closed_rnu_polygon
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X Y : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (e : Y ≅ X) (M : Sites.D true A X) :
    let h := pullback.fst i e.hom
    let j := pullback.snd i e.hom
    let U := pullback i e.hom
    let N := (Sites.rnu A X).obj M
    (scalarExtension φ U).map (Sites.closedPull A i e.hom N) ≫
      closedMap φ j ((Sites.pull A e.hom).obj N) ≫
      (closedUpper B j).map ((scalarExtension φ Y).map (Sites.rnuPull A e.hom M)) ≫
      (closedUpper B j).map (Sites.rnuScalar φ Y ((Sites.proPull A e.hom).obj M)) ≫
      (closedUpper B j).map ((Sites.rnu B Y).map
        ((Sites.proScalarPull φ e.hom).inv.app M)) =
    (Sites.scalarPull φ h).inv.app ((closedUpper A i).obj N) ≫
      (Sites.pull B h).map (closedMap φ i N) ≫
      (Sites.pull B h).map ((closedUpper B i).map (Sites.rnuScalar φ X M)) ≫
      Sites.closedPull B i e.hom ((Sites.rnu B X).obj ((Sites.scalar true φ X).obj M)) ≫
      (closedUpper B j).map (Sites.rnuPull B e.hom ((Sites.scalar true φ X).obj M)) := by
  dsimp only
  let h := pullback.fst i e.hom
  let j := pullback.snd i e.hom
  let U := pullback i e.hom
  let N := (Sites.rnu A X).obj M
  have hr := coefficient_rnu_pull_cube φ e.hom M
  have hr' := congrArg (fun z ↦
    (Sites.scalarPull φ e.hom).inv.app N ≫ z ≫
      (Sites.rnu B Y).map ((Sites.proScalarPull φ e.hom).inv.app M)) hr
  dsimp only [N] at hr'
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Functor.comp_obj, Category.comp_id] at hr'
  have ho := coefficient_map_closed_geometry φ i Y e N
  have hb := closed_geometric_naturality B i e (Sites.rnuScalar φ X M)
  dsimp only [Sites.scalar, _root_.id] at hr' hb ⊢
  rw [← (closedUpper B j).map_comp, ← (closedUpper B j).map_comp, ← hr']
  simp only [Functor.map_comp]
  rw [reassoc_of% ho, ← reassoc_of% hb]

/-- The closed geometric coefficient square is preserved by the actual site mates.
Source: blueprint latest, coefficient-extension proof, final paragraph.
(blueprint: lem-sf-coefficient-map-pro-closed-geometry).
Proof: invertible geometric pullback makes rnuPull an isomorphism. Naturality of
the ordinary coefficient mate along this isomorphism moves it through the closed
comparison. The site mate cube identifies the combined rnuScalar/rnuPull factors.
Use the ordinary closed square and naturality of ordinary closed geometric base
change at rnuScalar. Finally use the left site cube and sitePull naturality to
identify the two composites. Every site counit remains in its specified mate. -/
theorem coefficient_map_pro_closed_geometry
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Sites.ProClosedGeometry φ i := by
  intro Y e M _hM
  let h := pullback.fst i e.hom
  let j := pullback.snd i e.hom
  let U := pullback i e.hom
  let N := (Sites.rnu A X).obj M
  have := rnuPull_isIso A e M
  have hn := closed_coefficient_naturality_iso φ j
    (Sites.rnuPull A e.hom M) (inferInstance)
  have hs := (Sites.scalarSite φ U).hom.naturality
    ((closedUpper A j).map (Sites.rnuPull A e.hom M))
  have hs' := (Sites.scalarSite φ U).hom.naturality (Sites.closedPull A i e.hom N)
  have hp := (Sites.sitePull B h).hom.naturality (closedMap φ i N)
  have hp' := (Sites.sitePull B h).hom.naturality
    ((closedUpper B i).map (Sites.rnuScalar φ X M))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hs hs' hp hp'
  have hc := congrArg (fun z ↦
    (Sites.proScalarPull φ h).inv.app ((Sites.nu A Z).obj ((closedUpper A i).obj N)) ≫ z)
    (coefficient_site_pull_cube φ h ((closedUpper A i).obj N))
  simp only [Iso.inv_hom_id_app_assoc] at hc
  have hm := closed_rnu_polygon φ i e M
  dsimp only [Sites.scalar, _root_.id] at hm
  dsimp only [Sites.scalar, _root_.id] at hs hs' hp hp' hc
  unfold Sites.proClosedPull Sites.proClosedMap
  simp only [Sites.exceptional, Functor.comp_map, Functor.comp_obj, Functor.map_comp,
    Category.assoc,
    Sites.scalar, _root_.id]
  erw [reassoc_of% hs, ← (Sites.nu B U).map_comp_assoc, hn]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hs', reassoc_of% hc]
  have hν := congrArg (fun z ↦ (Sites.nu B U).map z) hm
  simp only [Functor.map_comp] at hν
  have hh := congrArg (fun z ↦
    (Sites.proScalarPull φ h).inv.app ((Sites.nu A Z).obj ((closedUpper A i).obj N)) ≫
      (Sites.proPull B h).map
        ((Sites.scalarSite φ Z).hom.app ((closedUpper A i).obj N)) ≫
      (Sites.sitePull B h).hom.app ((scalarExtension φ Z).obj ((closedUpper A i).obj N)) ≫
      (Sites.nu B U).map ((Sites.scalarPull φ h).hom.app ((closedUpper A i).obj N)) ≫ z) hν
  refine hh.trans ?_
  rw [← (Sites.nu B U).map_comp_assoc
    ((Sites.scalarPull φ h).hom.app ((closedUpper A i).obj N))
    ((Sites.scalarPull φ h).inv.app ((closedUpper A i).obj N)),
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← reassoc_of% hp, ← reassoc_of% hp']


end WeilConjectures.FiniteFreeCoefficients
