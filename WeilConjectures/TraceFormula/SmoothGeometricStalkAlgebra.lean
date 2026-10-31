/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationCanonicalMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap

import WeilConjectures.AlgebraicGeometry.SmoothStrictLocalBaseModel
import WeilConjectures.AlgebraicGeometry.SmoothStrictLocalClosedFibreModel
import WeilConjectures.AlgebraicGeometry.AffineCoordinateStrictLocalModel
import WeilConjectures.RingTheory.PolynomialStrictLocalCoordinateDimension
import WeilConjectures.RingTheory.StrictHenselizationFaithfullyFlat
import WeilConjectures.RingTheory.StrictHenselizationTriplesPresentation
import WeilConjectures.RingTheory.RegularLocalLocalization
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Smooth geometric stalk algebras

Source: literature/stacks-project/algebra.tex, more-algebra.tex, morphisms.tex
(Morphisms Tags 01VF and 01VB; Algebra Tags 05WS and 00OR; More on Algebra
Tags 06LN and 06LK; blueprint: lem-trf-smooth-geometric-stalk-algebra).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- The local-ring structure canonically supplied by strict henselization.
Source: Stacks Project, Tags 04HX and 06LJ (blueprint: lem-trf-smooth-geometric-stalk-algebra). -/
noncomputable instance strictHenselizationLocalRing
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) : IsLocalRing (Scheme.strictHenselizationRing s) :=
  Classical.choose (strictHenselizationLocalStructure s)

/-- The ring map induced by the canonical strict-henselization scheme map.
Source: Stacks Project, Tags 04HX, 03PS and 04GU
(blueprint: lem-trf-smooth-geometric-stalk-algebra). -/
noncomputable def strictHenselizationRingMap
    {S V : Scheme.{u}} (f : V ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (v : Spec (.of Ω) ⟶ V) :
    (Scheme.strictHenselizationRing (v ≫ f) : Type u) →+*
      (Scheme.strictHenselizationRing v : Type u) :=
  ((Scheme.ΓSpecIso (Scheme.strictHenselizationRing v)).hom.hom).comp
    (((Scheme.Hom.appTop (Scheme.strictHenselizationMap f v)).hom).comp
      (Scheme.ΓSpecIso (Scheme.strictHenselizationRing (v ≫ f))).inv.hom)

/-- Transport the canonical ring map along a displayed compatibility of points.
Source: Stacks Project, Tags 04HX, 03PS and 04GU
(blueprint: lem-trf-smooth-geometric-stalk-algebra). -/
noncomputable def strictHenselizationRingMapAlong
    {S V : Scheme.{u}} (f : V ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (v : Spec (.of Ω) ⟶ V) (hv : v ≫ f = s) :
    (Scheme.strictHenselizationRing s : Type u) →+*
      (Scheme.strictHenselizationRing v : Type u) :=
  hv ▸ strictHenselizationRingMap f v

/-- The affine-space coordinate in a strict geometric stalk.
Source: Stacks Project, Tag 00OR (blueprint: lem-trf-smooth-geometric-stalk-algebra). -/
noncomputable def strictHenselizationAffineCoordinate
    {S V : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (v : Spec (.of Ω) ⟶ V) (r : ℕ)
    (e : V ≅ 𝔸(ULift.{u} (Fin r); S)) (i : ULift.{u} (Fin r)) :
    (Scheme.strictHenselizationRing v : Type u) :=
  (Scheme.ΓSpecIso (Scheme.strictHenselizationRing v)).hom.hom
    ((Scheme.Hom.appTop
      (Scheme.strictHenselizationStructuralMap v ≫ e.hom)).hom
      (AffineSpace.coord S i))

private theorem strictHenselizationRingMap_eq
    {S V : Scheme.{u}} (f : V ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (v : Spec (.of Ω) ⟶ V) :
    strictHenselizationRingMap f v = (Spec.preimage (Scheme.strictHenselizationMap f v)).hom := by
  change ((Scheme.ΓSpecIso (Scheme.strictHenselizationRing (v ≫ f))).inv ≫
    (Scheme.strictHenselizationMap f v).appTop ≫
    (Scheme.ΓSpecIso (Scheme.strictHenselizationRing v)).hom).hom = _
  have h := Scheme.ΓSpecIso_inv_naturality
    (Spec.preimage (Scheme.strictHenselizationMap f v))
  rw [Spec.map_preimage] at h
  rw [← Category.assoc, ← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem presentation_repoint
    (R K K' H : Type u) [CommRing R] [IsLocalRing R] [Field K] [Field K']
    [Algebra (IsLocalRing.ResidueField R) K] [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra (IsLocalRing.ResidueField R) K'] [IsSepClosure (IsLocalRing.ResidueField R) K']
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [Algebra R K'] [IsScalarTower R (IsLocalRing.ResidueField R) K']
    [CommRing H] [Algebra R H] (e : K ≃ₐ[R] K')
    (P : Algebra.StrictHenselizationPresentationIn.{u, u} R K H) :
    Nonempty (Algebra.StrictHenselizationPresentationIn.{u, u} R K' H) := by
  let P₀ : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Algebra.Etale R X.left
  let P₁ : ObjectProperty (Over (CommAlgCat.of R K')) := fun X ↦ Algebra.Etale R X.left
  let E := (Over.mapIso (CommAlgCat.isoMk e)).symm
  let F := P₀.lift (P₁.ι ⋙ E.functor) (fun X ↦ X.property)
  let G := P₁.lift (P₀.ι ⋙ E.inverse) (fun X ↦ X.property)
  let E' : P₁.FullSubcategory ≌ P₀.FullSubcategory := {
    functor := F
    inverse := G
    unitIso := NatIso.ofComponents
      (fun X ↦ ObjectProperty.isoMk _ (E.unitIso.app X.obj))
      (by intro X Y f; apply ObjectProperty.hom_ext; exact E.unitIso.hom.naturality f.hom)
    counitIso := NatIso.ofComponents
      (fun X ↦ ObjectProperty.isoMk _ (E.counitIso.app X.obj))
      (by intro X Y f; apply ObjectProperty.hom_ext; exact E.counitIso.hom.naturality f.hom)
    functor_unitIso_comp X := by
      apply ObjectProperty.hom_ext
      exact E.functor_unit_comp X.obj }
  exact ⟨{
    cocone := P.cocone.whisker E'.functor
    isColimit := P.isColimit.whiskerEquivalence E'
    identification := P.identification }⟩

private theorem presentation_flat
    (R K H : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K] [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing H] [Algebra R H]
    (P : Algebra.StrictHenselizationPresentationIn.{u, u} R K H) :
    RingHom.Flat (algebraMap R H) := by
  have hH : Algebra.IsStrictHenselization R K H :=
    ⟨P.cocone, ⟨P.isColimit⟩, ⟨P.identification⟩⟩
  obtain ⟨p, hp, a, hs, ι, ⟨hc⟩, hρ⟩ := hH.triples_presentation R K H
  let := a
  have := hs
  exact (Scheme.strictHenselization_faithfullyFlat (.of R) p hp K
    (CategoryTheory.Limits.Cocone.mk (.of H) ι) hc
    (CommRingCat.ofHom (algebraMap R H)) hρ).flat

private theorem smooth_strictMap_flat_local
    {S V : Scheme.{u}} (f : V ⟶ S) [Smooth f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) :
    RingHom.Flat (strictHenselizationRingMap f v) ∧
      IsLocalHom (strictHenselizationRingMap f v) := by
  obtain ⟨_, hA, hB, _, hflat, _, hlocal, _, _, _, _, _,
    a, _, b, t, H, hH, aH, P, hLH, θ, β, _, hβ, _⟩ :=
    Scheme.SmoothStrictLocalBaseModel.smooth_strictLocal_base_model f v
  let := a
  let := b
  have := t
  let := hH
  let := aH
  have hcomp := hflat.comp (presentation_flat _ _ _ P)
  rw [← hβ] at hcomp
  have hflat' := (RingHom.Flat.comp_iff_of_bijective_left β.bijective).mp hcomp
  rw [strictHenselizationRingMap_eq]
  exact ⟨hflat', hlocal⟩

private theorem flat_quotientMap
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat) (I : Ideal A) :
    RingHom.Flat (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map) := by
  let := φ.toAlgebra
  have : Module.Flat A B := hφ
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  have h : Module.Flat (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    Module.Flat.of_linearEquiv e.toLinearEquiv
  exact RingHom.flat_algebraMap_iff.mpr h

private theorem local_quotientMap
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing B]
    {I : Ideal A} {J : Ideal B} [Nontrivial (B ⧸ J)]
    (φ : A →+* B) [IsLocalHom φ] (h : I ≤ J.comap φ) :
    IsLocalHom (Ideal.quotientMap J φ h) := by
  have := IsLocalHom.of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  constructor
  intro a ha
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.quotientMap_mk] at ha
  exact (Ideal.Quotient.mk I).isUnit_map
    (isUnit_of_map_unit φ a (isUnit_of_map_unit (Ideal.Quotient.mk J) (φ a) ha))

private theorem smooth_closed_fibre_regular
    {S V : Scheme.{u}} (f : V ⟶ S) [Smooth f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) :
    IsRegularRing (Scheme.strictHenselizationRing v ⧸ Ideal.map
      (strictHenselizationRingMap f v)
      (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing (v ≫ f)))) := by
  obtain ⟨_, hker, _, z, _, _, _, _, _, eW, _, _, _, eQ, _, _, hreg, _⟩ :=
    Scheme.smooth_strict_local_closed_fibre_model f v
  have := hreg
  have hreg' := (IsRegularLocalRing.localization_at_prime_and_isRegularRing
    (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing z))).2
  have := hreg'
  have h := IsRegularRing.of_ringEquiv eQ.symm
  change IsRegularRing (Scheme.strictHenselizationRing v ⧸ Ideal.map
    (Spec.preimage (Scheme.strictHenselizationMap f v)).hom
    (RingHom.ker (Scheme.strictHenselizationPointEvaluation (v ≫ f)))) at h
  rw [hker] at h
  rw [strictHenselizationRingMap_eq]
  exact h

private theorem strictMapAlong_over
    {S V : Scheme.{u}} (f : V ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (v : Spec (.of Ω) ⟶ V) (hv : v ≫ f = s) :
    Spec.map (CommRingCat.ofHom (strictHenselizationRingMapAlong f s v hv)) ≫
      Scheme.strictHenselizationStructuralMap s =
        Scheme.strictHenselizationStructuralMap v ≫ f := by
  subst s
  simpa only [strictHenselizationRingMapAlong, strictHenselizationRingMap_eq,
    CommRingCat.ofHom_hom, Spec.map_preimage] using Scheme.strictHenselizationMap_over f v

private theorem strictMapAlong_point
    {S V : Scheme.{u}} (f : V ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (v : Spec (.of Ω) ⟶ V) (hv : v ≫ f = s) :
    Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation v)) ≫
      Spec.map (CommRingCat.ofHom (strictHenselizationRingMapAlong f s v hv)) =
        Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation s)) := by
  subst s
  have hp := (Classical.choose_spec (Scheme.strictHenselizationMap_existsUnique f v)).1.2
  change Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation v)) ≫
    Scheme.strictHenselizationMap f v = _ at hp
  simpa only [strictHenselizationRingMapAlong, strictHenselizationRingMap_eq,
    CommRingCat.ofHom_hom, Spec.map_preimage] using hp

private theorem strictMapAlong_unique
    {S V : Scheme.{u}} (f : V ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (v : Spec (.of Ω) ⟶ V) (hv : v ≫ f = s)
    (ψ : Scheme.strictHenselizationRing s →+* Scheme.strictHenselizationRing v)
    (hb : Spec.map (CommRingCat.ofHom ψ) ≫ Scheme.strictHenselizationStructuralMap s =
      Scheme.strictHenselizationStructuralMap v ≫ f)
    (hp : Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation v)) ≫
      Spec.map (CommRingCat.ofHom ψ) =
        Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation s))) :
    ψ = strictHenselizationRingMapAlong f s v hv := by
  subst s
  have hψ := (Classical.choose_spec (Scheme.strictHenselizationMap_existsUnique f v)).2
    (Spec.map (CommRingCat.ofHom ψ)) ⟨hb, hp⟩
  change _ = Scheme.strictHenselizationMap f v at hψ
  have hh : CommRingCat.ofHom ψ = Spec.preimage (Scheme.strictHenselizationMap f v) :=
    Spec.map_injective (hψ.trans (Spec.map_preimage _).symm)
  simpa only [strictHenselizationRingMapAlong, strictHenselizationRingMap_eq,
    CommRingCat.hom_ofHom] using congrArg CommRingCat.Hom.hom hh

private theorem strictMapAlong_comp
    {S V W : Scheme.{u}} (f : V ⟶ S) (g : W ⟶ V) (h : W ⟶ S)
    (hg : g ≫ f = h) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (v : Spec (.of Ω) ⟶ V) (w : Spec (.of Ω) ⟶ W)
    (hv : v ≫ f = s) (hw : w ≫ g = v) (hw' : w ≫ h = s) :
    (strictHenselizationRingMapAlong g v w hw).comp
      (strictHenselizationRingMapAlong f s v hv) =
        strictHenselizationRingMapAlong h s w hw' := by
  apply strictMapAlong_unique h s w hw'
  · change (Spec.map (CommRingCat.ofHom
      (strictHenselizationRingMapAlong f s v hv) ≫ CommRingCat.ofHom
        (strictHenselizationRingMapAlong g v w hw))) ≫ _ = _
    rw [Spec.map_comp, Category.assoc, strictMapAlong_over, ← Category.assoc,
      strictMapAlong_over, Category.assoc, hg]
  · change Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationPointEvaluation w)) ≫
      Spec.map (CommRingCat.ofHom (strictHenselizationRingMapAlong f s v hv) ≫
        CommRingCat.ofHom (strictHenselizationRingMapAlong g v w hw)) = _
    rw [Spec.map_comp, ← Category.assoc, strictMapAlong_point, strictMapAlong_point]

private theorem coordinate_ringMap_eq
    {X Y : Scheme.{u}} (g : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (h : y = x ≫ g) :
    Scheme.AffineCoordinateStrictLocal.ringMap g x y h =
      strictHenselizationRingMapAlong g y x h.symm := by
  subst y
  simp only [Scheme.AffineCoordinateStrictLocal.ringMap, eqToHom_refl, Category.comp_id,
    strictHenselizationRingMapAlong, strictHenselizationRingMap_eq]

private theorem coordinate_baseMap_eq
    {S V : Scheme.{u}} (r : ℕ) (e : V ≅ 𝔸(ULift.{u} (Fin r); S))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V) :
    Scheme.AffineCoordinateStrictLocal.baseMap r e v =
      strictHenselizationRingMap (Scheme.AffineCoordinateStrictLocal.projection r e) v := by
  exact coordinate_ringMap_eq _ _ _ rfl

private theorem smooth_strictMapAlong_flat
    {S V : Scheme.{u}} (f : V ⟶ S) [Smooth f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (v : Spec (.of Ω) ⟶ V) (hv : v ≫ f = s) :
    RingHom.Flat (strictHenselizationRingMapAlong f s v hv) := by
  subst s
  exact (smooth_strictMap_flat_local f v).1

private theorem affine_coordinate_flat
    {S V : Scheme.{u}} (r : ℕ) (e : V ≅ 𝔸(ULift.{u} (Fin r); S))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
    (K : Set (ULift.{u} (Fin r)))
    (hK : ∀ i ∈ K, strictHenselizationAffineCoordinate v r e i ∈
      IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing v)) :
    RingHom.Flat ((Ideal.Quotient.mk
      (Scheme.AffineCoordinateStrictLocal.coordinateIdeal r e v K)).comp
      (Scheme.AffineCoordinateStrictLocal.baseMap r e v)) := by
  classical
  let g := Scheme.AffineCoordinateStrictLocal.projection r e
  let : IsLocalRing (Scheme.AffineCoordinateStrictLocal.Base r e v) :=
    strictHenselizationLocalRing (v ≫ g)
  obtain ⟨M⟩ := Scheme.AffineCoordinateStrictLocal.exists_model r e v K hK
  let j := Scheme.AffineCoordinateStrictLocal.inclusion r e K
  let gK := 𝔸({i : ULift.{u} (Fin r) // i ∉ K}; S) ↘ S
  have hj : j ≫ g = gK := by
    simp only [j, g, Scheme.AffineCoordinateStrictLocal.inclusion,
      Scheme.AffineCoordinateStrictLocal.projection, Category.assoc,
      Iso.inv_hom_id_assoc, AffineSpace.homOfVector_over, gK]
  have hw : M.point ≫ gK = v ≫ g := by
    calc
      M.point ≫ gK = M.point ≫ (j ≫ g) := congrArg (fun z ↦ M.point ≫ z) hj.symm
      _ = (M.point ≫ j) ≫ g := (Category.assoc _ _ _).symm
      _ = v ≫ g := congrArg (fun z ↦ z ≫ g) M.point_eq.symm
  have : Smooth gK := M.smooth
  have hflat' := smooth_strictMapAlong_flat gK (v ≫ g) M.point hw
  have heq := strictMapAlong_comp g j gK hj (v ≫ g) v M.point rfl M.point_eq.symm hw
  have hqm := M.quotientIso_map
  rw [coordinate_ringMap_eq] at hqm
  have hcomp := congrArg (fun z ↦ M.quotientIso.toRingHom.comp z) heq
  rw [← RingHom.comp_assoc, hqm] at hcomp
  change (Ideal.Quotient.mk _).comp (strictHenselizationRingMap g v) = _ at hcomp
  rw [coordinate_baseMap_eq, hcomp]
  exact hflat'.comp (RingHom.Flat.of_bijective M.quotientIso.bijective)

private theorem flat_quotientMap_sup
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (J : Ideal B)
    (hφ : RingHom.Flat ((Ideal.Quotient.mk J).comp φ)) (I : Ideal A) :
    RingHom.Flat (Ideal.quotientMap (I.map φ ⊔ J) φ
      (Ideal.le_comap_map.trans (Ideal.comap_mono le_sup_left))) := by
  let ψ := (Ideal.Quotient.mk J).comp φ
  have h := flat_quotientMap ψ hφ I
  let E₀ := Ideal.quotEquivOfEq (Ideal.map_map (I := I) φ (Ideal.Quotient.mk J)).symm
  let E := (E₀.trans (DoubleQuot.quotQuotEquivQuotSup J (I.map φ))).trans
    (Ideal.quotEquivOfEq (sup_comm J (I.map φ)))
  have hE : RingHom.Flat E.toRingHom := RingHom.Flat.of_bijective E.bijective
  have h' := h.comp hE
  have heq : E.toRingHom.comp
      (Ideal.quotientMap (I.map ψ) ψ Ideal.le_comap_map) =
      Ideal.quotientMap (I.map φ ⊔ J) φ
        (Ideal.le_comap_map.trans (Ideal.comap_mono le_sup_left)) := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    rfl
  rwa [heq] at h'

open Scheme.AffineCoordinateStrictLocal in
private theorem affine_coordinate_dimension
    {S V : Scheme.{u}} (r : ℕ) (e : V ≅ 𝔸(ULift.{u} (Fin r); S))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ V)
    (K : Finset (ULift.{u} (Fin r)))
    (hK : ∀ i ∈ K, strictHenselizationAffineCoordinate v r e i ∈
      IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing v)) :
    let : IsLocalRing (Base r e v) := strictHenselizationLocalRing (v ≫ projection r e)
    IsRegularRing (Scheme.strictHenselizationRing v ⧸
      (fibreIdeal r e v ⊔ coordinateIdeal r e v K)) ∧
      ringKrullDim (Scheme.strictHenselizationRing v ⧸ fibreIdeal r e v) =
        ringKrullDim (Scheme.strictHenselizationRing v ⧸
          (fibreIdeal r e v ⊔ coordinateIdeal r e v K)) + K.card := by
  classical
  let : IsLocalRing (Base r e v) := strictHenselizationLocalRing (v ≫ projection r e)
  obtain ⟨M⟩ := exists_model r e v K hK
  let F := M.fibres
  have := F.prime0
  have := F.prime1
  let := F.residueAlgebra0
  let := F.residueAlgebra1
  let := F.ring0
  let := F.ring1
  let := F.modelAlgebra0
  let := F.modelAlgebra1
  let := F.closureAlgebra0
  let := F.closureAlgebra1
  have := F.tower0
  have := F.tower1
  let q := RingHom.ker F.polynomialPoint
  let q' := RingHom.ker F.quotientPoint
  let L := polynomialIdeal r e v (K : Set (Index.{u} r))
  have hq : q = q'.comap (Ideal.Quotient.mk L) := by
    rw [RingHom.comap_ker, F.quotientPoint_eq]
  let γ : q.ResidueField ≃+* q'.ResidueField := RingEquiv.ofBijective
    (Ideal.ResidueField.map q q' (Ideal.Quotient.mk L) hq)
    ((RingHom.surjectiveOnStalks_of_surjective (f := Ideal.Quotient.mk L)
      Ideal.Quotient.mk_surjective).residueFieldMap_bijective q q' hq)
  let C₀ := separableClosure q.ResidueField Ω
  let C₁ := separableClosure q'.ResidueField Ω
  let cField : Field C₁ := inferInstance
  let a₁ : Algebra q'.ResidueField C₁ := inferInstance
  have hsep₁ : IsSepClosure q'.ResidueField C₁ := inferInstance
  let a₀ : Algebra q.ResidueField C₁ :=
    ((algebraMap q'.ResidueField C₁).comp γ.toRingHom).toAlgebra
  have hsep : Algebra.IsSeparable q.ResidueField C₁ :=
    Algebra.IsSeparable.of_equiv_equiv γ.symm (RingEquiv.refl C₁) (by
      apply RingHom.ext
      intro x
      change algebraMap q'.ResidueField C₁ (γ (γ.symm x)) = algebraMap q'.ResidueField C₁ x
      rw [γ.apply_symm_apply])
  have : IsSepClosed C₁ := IsSepClosure.sep_closed q'.ResidueField
  have hsep₀ : IsSepClosure q.ResidueField C₁ := ⟨inferInstance, hsep⟩
  let ac₀ : Algebra (Localization.AtPrime q) C₁ :=
    ((algebraMap q.ResidueField C₁).comp
      (IsLocalRing.residue (Localization.AtPrime q))).toAlgebra
  have ht₀ : IsScalarTower (Localization.AtPrime q) q.ResidueField C₁ :=
    IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let ac₁ : Algebra (Localization.AtPrime q') C₁ := F.closureAlgebra1
  have ht₁ : IsScalarTower (Localization.AtPrime q') q'.ResidueField C₁ := F.tower1
  let ε := (IsSepClosure.equiv q.ResidueField C₀ C₁).restrictScalars (Localization.AtPrime q)
  obtain ⟨P₀⟩ := presentation_repoint (Localization.AtPrime q) C₀ C₁ F.H0 ε F.presentation0
  have hL : L = Ideal.span (Set.range (fun i : K ↦
      (MvPolynomial.X i.1 :
        MvPolynomial (Index.{u} r) (IsLocalRing.ResidueField (Base r e v))))) := by
    unfold L polynomialIdeal
    congr 1
    exact Set.image_eq_range _ _
  have hΩ : algebraMap q.ResidueField C₁ = (algebraMap q'.ResidueField C₁).comp
      (Ideal.ResidueField.map q q' (Ideal.Quotient.mk L) hq) := rfl
  obtain ⟨_, _, _, hreg, _, _, _, hdim⟩ :=
    @MvPolynomial.polynomial_strictLocal_coordinate_dimension.{u, u, u}
      (IsLocalRing.ResidueField (Base r e v)) _ (Index.{u} r) _ K L hL q _ q' _ hq
      C₁ F.H0 F.H1 cField a₀ hsep₀ a₁ hsep₁ hΩ ac₀ ht₀ ac₁ ht₁
      F.ring0 F.modelAlgebra0 F.ring1 F.modelAlgebra1 P₀ F.presentation1
  have := hreg
  have hreg' := (IsRegularLocalRing.localization_at_prime_and_isRegularRing
    (IsLocalRing.maximalIdeal F.H1)).2
  have := hreg'
  refine ⟨IsRegularRing.of_ringEquiv F.iso1.symm, ?_⟩
  rw [F.iso0.ringKrullDim, F.iso1.ringKrullDim]
  exact hdim

/--
For a smooth morphism, strict local rings at compatible geometric points are
Noetherian local rings, the canonical map is flat and local, and its closed fibre
is regular.  Quotients by ideals below the maximal ideal retain these properties.
In the relative affine-space case the canonical coordinate sections cut regular
fibres and satisfy the dimension formula.

Source: Morphisms Tags 01VF and 01VB, Algebra Tags 05WS and 00OR, More on
Algebra Tags 06LN and 06LK (blueprint: lem-trf-smooth-geometric-stalk-algebra).

Proof plan, following the eight steps in the node:
1. Choose Noetherian affine neighbourhoods. The affine stalk-localization comparison and
   Noetherian localization identify their local rings; the affine strict-local comparison
   and Noetherian strict-henselization theorem make both strict local rings Noetherian.
   The comparison also identifies maximal-ideal membership with zero geometric evaluation.
2. Base change `V` to the strict localization of `S`. Functoriality lifts the common geometric
   point. The affine-chart structural map is ind-etale, so ind-etale strict-local invariance
   identifies the resulting strict local ring with `B`. Functorial uniqueness identifies
   its map from `A` with the canonical map used here.
3. Smooth-flatness makes the ordinary local map flat. Faithful flatness of its strict
   henselization and transitivity give flatness of the canonical map. Functoriality gives
   locality.
4. Base change to the residue field of `A`. The cartesian closed-immersion strict-localization
   theorem identifies its strict local ring with `B / mA B`. Smoothness over a field and
   preservation of regularity under strict henselization give regularity.
5. Flat quotient base change gives flatness over `A / I`. The quotient-local-structure
   theorem gives locality because `I` lies below `mA`. The inclusion `IB ≤ mA B` identifies
   the two displayed fibre quotients by the map fixing every quotient class.
6. Setting the selected coordinates to zero gives affine space in the remaining variables.
   Geometric evaluation makes the point factor through this closed subscheme. The cartesian
   strict-localization theorem identifies its ring with the coordinate quotient. Repeat
   steps 2--3 for its smooth projection, then apply quotient base change and quotient-local
   structure. Noetherianity descends from `B`.
7. On the closed fibre write `P` for the polynomial ring over the residue field of `A`,
   `q` for the geometric-point prime, and `L` for the selected-variable ideal. The affine
   comparison identifies the two fibre rings with strict henselizations of `P_q` and
   `(P/L)_(q/L)`. Polynomial regularity and strict-henselization regularity apply to both.
8. The subring `D` in the selected variables contracts `q` to its origin ideal `n`.
   The polynomial map `D → P` is smooth and flat. The flat height formula expresses
   `dim P_q` as `dim D_n + dim (P/L)_(q/L)`. The polynomial-origin dimension is `K.card`;
   preservation of dimension under strict henselization gives the displayed formula.
   This includes empty and full coordinate subsets and does not assume `q` maximal.
-/
theorem smooth_geometric_stalk_algebra
    {S V : Scheme.{u}} (f : V ⟶ S) [IsLocallyNoetherian S] [IsLocallyNoetherian V]
    [Smooth f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (v : Spec (.of Ω) ⟶ V)
    (hv : v ≫ f = s) :
    IsNoetherianRing (Scheme.strictHenselizationRing s) ∧ IsNoetherianRing
          (Scheme.strictHenselizationRing v) ∧
      IsLocalRing (Scheme.strictHenselizationRing s) ∧ IsLocalRing (Scheme.strictHenselizationRing
          v) ∧
      RingHom.Flat (strictHenselizationRingMapAlong f s v hv) ∧ IsLocalHom
          (strictHenselizationRingMapAlong f s v hv) ∧
      IsRegularRing ((Scheme.strictHenselizationRing v) ⧸ Ideal.map
          (strictHenselizationRingMapAlong f s v hv) (IsLocalRing.maximalIdeal
          (Scheme.strictHenselizationRing s))) ∧
      (∀ (I : Ideal (Scheme.strictHenselizationRing s)), ∀ _hI : I ≤ (IsLocalRing.maximalIdeal
          (Scheme.strictHenselizationRing s)),
        RingHom.Flat (Ideal.quotientMap (Ideal.map (strictHenselizationRingMapAlong f s v hv) I)
          (strictHenselizationRingMapAlong f s v hv) Ideal.le_comap_map) ∧
          IsLocalHom (Ideal.quotientMap (Ideal.map (strictHenselizationRingMapAlong f s v hv) I)
          (strictHenselizationRingMapAlong f s v hv) Ideal.le_comap_map) ∧
          (∃ E : ((Scheme.strictHenselizationRing v) ⧸ (Ideal.map (strictHenselizationRingMapAlong
          f s v hv) I ⊔ Ideal.map (strictHenselizationRingMapAlong f s v hv)
          (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing s)))) ≃+*
            ((Scheme.strictHenselizationRing v) ⧸ Ideal.map (strictHenselizationRingMapAlong f s v
          hv) (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing s))), ∀ b :
          (Scheme.strictHenselizationRing v),
              E (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ b)) ∧
      (∀ (r : ℕ) (e : V ≅ 𝔸(ULift.{u} (Fin r); S))
        (_he : e.hom ≫ (𝔸(ULift.{u} (Fin r); S) ↘ S) = f)
        (K : Finset (ULift.{u} (Fin r)))
        (_hK : ∀ i, i ∈ K → strictHenselizationAffineCoordinate v r e i ∈
          (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing v)))
        (I : Ideal (Scheme.strictHenselizationRing s)), ∀ _hI : I ≤ (IsLocalRing.maximalIdeal
          (Scheme.strictHenselizationRing s)),
        IsNoetherianRing
          ((Scheme.strictHenselizationRing v) ⧸ (Ideal.map (strictHenselizationRingMapAlong f s v
          hv) I ⊔ Ideal.span (Set.range
            (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1)))) ∧
        IsLocalRing
          ((Scheme.strictHenselizationRing v) ⧸ (Ideal.map (strictHenselizationRingMapAlong f s v
          hv) I ⊔ Ideal.span (Set.range
            (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1)))) ∧
        RingHom.Flat (Ideal.quotientMap
          (Ideal.map (strictHenselizationRingMapAlong f s v hv) I ⊔ Ideal.span (Set.range
            (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1)))
          (strictHenselizationRingMapAlong f s v hv)
          (Ideal.le_comap_map.trans (Ideal.comap_mono le_sup_left))) ∧
        IsRegularRing
          ((Scheme.strictHenselizationRing v) ⧸ (Ideal.map (strictHenselizationRingMapAlong f s v
          hv) (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing s)) ⊔ Ideal.span
          (Set.range
            (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1)))) ∧
        (∃ E :
          ((Scheme.strictHenselizationRing v) ⧸ ((Ideal.map (strictHenselizationRingMapAlong f s v
          hv) I ⊔ Ideal.span (Set.range
            (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1))) ⊔ Ideal.map
          (strictHenselizationRingMapAlong f s v hv) (IsLocalRing.maximalIdeal
          (Scheme.strictHenselizationRing s)))) ≃+*
          ((Scheme.strictHenselizationRing v) ⧸ (Ideal.map (strictHenselizationRingMapAlong f s v
          hv) (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing s)) ⊔ Ideal.span
          (Set.range
            (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1)))),
          ∀ b : (Scheme.strictHenselizationRing v), E (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk
          _ b) ∧
        ringKrullDim ((Scheme.strictHenselizationRing v) ⧸ Ideal.map
          (strictHenselizationRingMapAlong f s v hv) (IsLocalRing.maximalIdeal
          (Scheme.strictHenselizationRing s))) =
          ringKrullDim
            ((Scheme.strictHenselizationRing v) ⧸ (Ideal.map (strictHenselizationRingMapAlong f s
          v hv) (IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing s)) ⊔ Ideal.span
          (Set.range
              (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1)))) + K.card) := by
  subst s
  dsimp only [strictHenselizationRingMapAlong]
  have hnoeth := (Scheme.SmoothStrictLocalBaseModel.smooth_strictLocal_base_model f v).2
  obtain ⟨_, _, _, _, _, _, _, _, hn, _⟩ := hnoeth
  obtain ⟨hA, hB⟩ := hn inferInstance inferInstance
  have := hA
  have := hB
  obtain ⟨hflat, hlocal⟩ := smooth_strictMap_flat_local f v
  let φ := strictHenselizationRingMap f v
  change IsNoetherianRing _ ∧ IsNoetherianRing _ ∧ IsLocalRing _ ∧ IsLocalRing _ ∧
    φ.Flat ∧ IsLocalHom φ ∧ _
  have : IsLocalHom φ := hlocal
  refine ⟨hA, hB, inferInstance, inferInstance, hflat, hlocal,
    smooth_closed_fibre_regular f v, ?_, ?_⟩
  · intro I hI
    have hIB : I.map φ ≤ IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing v) := by
      rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
      exact hI
    have : Nontrivial (Scheme.strictHenselizationRing v ⧸ I.map φ) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hIB)
    refine ⟨flat_quotientMap φ hflat I, local_quotientMap φ Ideal.le_comap_map, ?_⟩
    refine ⟨Ideal.quotEquivOfEq (sup_eq_right.mpr (Ideal.map_mono hI)), ?_⟩
    intro b
    rfl
  · intro r e he K hK I hI
    subst f
    have hbase : Scheme.AffineCoordinateStrictLocal.baseMap r e v = φ :=
      coordinate_baseMap_eq r e v
    let J : Ideal (Scheme.strictHenselizationRing v) :=
      Ideal.span (Set.range (fun i : K ↦ strictHenselizationAffineCoordinate v r e i.1))
    have hJ : Scheme.AffineCoordinateStrictLocal.coordinateIdeal r e v K = J := by
      unfold Scheme.AffineCoordinateStrictLocal.coordinateIdeal J
      congr 1
      exact Set.image_eq_range _ _
    have hraw : RingHom.Flat ((Ideal.Quotient.mk J).comp φ) := by
      have h := affine_coordinate_flat r e v K hK
      rwa [hbase, hJ] at h
    have hdim := affine_coordinate_dimension r e v K hK
    dsimp only at hdim
    unfold Scheme.AffineCoordinateStrictLocal.fibreIdeal at hdim
    rw [hbase, hJ] at hdim
    have hIB : I.map φ ≤ IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing v) := by
      rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
      exact hI
    have hJB : J ≤ IsLocalRing.maximalIdeal (Scheme.strictHenselizationRing v) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hK i.1 i.2
    have : Nontrivial (Scheme.strictHenselizationRing v ⧸ (I.map φ ⊔ J)) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
          (sup_le hIB hJB))
    refine ⟨inferInstance, IsLocalRing.of_surjective' (Ideal.Quotient.mk _)
      Ideal.Quotient.mk_surjective, flat_quotientMap_sup φ J hraw I, hdim.1, ?_, hdim.2⟩
    have hIm : I.map φ ≤ (IsLocalRing.maximalIdeal
        (Scheme.strictHenselizationRing (v ≫ (e.hom ≫ (𝔸(ULift.{u} (Fin r); S) ↘ S))))).map φ :=
      Ideal.map_mono hI
    have hEq : (I.map φ ⊔ J) ⊔ (IsLocalRing.maximalIdeal
        (Scheme.strictHenselizationRing (v ≫ (e.hom ≫ (𝔸(ULift.{u} (Fin r); S) ↘ S))))).map φ =
        (IsLocalRing.maximalIdeal
          (Scheme.strictHenselizationRing
            (v ≫ (e.hom ≫ (𝔸(ULift.{u} (Fin r); S) ↘ S))))).map φ ⊔ J := by
      rw [sup_right_comm, sup_eq_right.mpr hIm]
    exact ⟨Ideal.quotEquivOfEq hEq, fun _ ↦ rfl⟩

end AlgebraicGeometry
