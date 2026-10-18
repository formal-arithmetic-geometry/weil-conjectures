/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NP and G8
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.Irreducible
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Reduction commutes with a generic fibre

Source: Stacks Project, Tag 054Z, `lemma-reduction-generic-fibre`
(blueprint: lem-pur-reduction-generic-fibre).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The fibre ring of a reduced algebra at a minimal prime is reduced (Stacks 054Z). -/
private theorem reduced_fiber_ring
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] [_root_.IsReduced B]
    (p : Ideal R) [p.IsPrime] (hp : p ∈ minimalPrimes R) :
    _root_.IsReduced (p.Fiber B) := by
  let Rp := Localization.AtPrime p
  let L := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)
  have : Ring.KrullDimLE 0 Rp := Ring.KrullDimLE.of_isLocalization p hp Rp
  have hzero : (IsLocalRing.maximalIdeal Rp).map (algebraMap Rp L) = ⊥ := by
    apply le_bot_iff.mp
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change algebraMap Rp L x = 0
    exact ((Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal.mpr hx).map
      (algebraMap Rp L)).eq_zero
  let : Algebra B (p.Fiber B) := Algebra.TensorProduct.rightAlgebra
  let e := Ideal.Fiber.algEquivQuotient (S := B) p
  have : _root_.IsReduced (L ⧸ (IsLocalRing.maximalIdeal Rp).map (algebraMap Rp L)) := by
    rw [hzero]
    exact (Ideal.isRadical_iff_quotient_reduced _).mp Ideal.isRadical_bot
  exact isReduced_of_injective e.toRingHom e.injective

/-- Transfer the reduced fibre-ring calculation through the canonical affine fibre iso. -/
private theorem reduced_fiber_spec
    {R B : CommRingCat.{u}} [IsReduced (Spec B)] (f : Spec B ⟶ Spec R)
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R) : IsReduced (f.fiber p) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = f := ⟨_, Spec.map_preimage _⟩
  let : Algebra R B := φ.hom.toAlgebra
  have : _root_.IsReduced B := (affine_isReduced_iff B).mp inferInstance
  have : _root_.IsReduced (p.asIdeal.Fiber B) := reduced_fiber_ring p.asIdeal hp
  have hred : IsReduced (Spec (.of (p.asIdeal.Fiber B))) := inferInstance
  let e := Spec.fiberToSpecResidueFieldIso R B p
  exact @isReduced_of_isOpenImmersion _ _ e.hom.left inferInstance hred

/-- Pull back an affine source cover and use reducedness locally on the fibre. -/
private theorem reduced_fiber_affine_base
    {R : CommRingCat.{u}} {X : Scheme.{u}} [IsReduced X] (f : X ⟶ Spec R)
    (p : PrimeSpectrum R) (hp : p.asIdeal ∈ minimalPrimes R) : IsReduced (f.fiber p) := by
  let 𝒰 := X.affineCover.pullback₁ (f.fiberι p)
  have (i : X.affineCover.I₀) : IsReduced (𝒰.X i) := by
    have : IsReduced (X.affineCover.X i) :=
      isReduced_of_isOpenImmersion (X.affineCover.f i)
    have hred : IsReduced ((X.affineCover.f i ≫ f).fiber p) :=
      @reduced_fiber_spec _ _ (show IsReduced (X.affineCover.X i) from inferInstance)
        (X.affineCover.f i ≫ f) p hp
    let e := Limits.pullbackSymmetry (f.fiberι p) (X.affineCover.f i) ≪≫
      Limits.pullbackRightPullbackFstIso f ((Spec R).fromSpecResidueField p)
        (X.affineCover.f i)
    exact @isReduced_of_isOpenImmersion _ _ e.hom inferInstance hred
  exact IsReduced.of_openCover _ 𝒰

/-- Reduce the base to an affine neighbourhood of the generic point (Stacks 054Z). -/
private theorem reduced_fiber_generic
    {X T : Scheme.{u}} [IsReduced X] (f : X ⟶ T) (η : T)
    (hη : closure ({η} : Set T) ∈ irreducibleComponents T) : IsReduced (f.fiber η) := by
  obtain ⟨i, p, rfl⟩ := T.affineCover.exists_eq η
  let j := T.affineCover.f i
  have hp : closure ({p} : Set (T.affineCover.X i)) ∈
      irreducibleComponents (T.affineCover.X i) := by
    rw [j.isOpenEmbedding.closure_eq_preimage_closure_image, Set.image_singleton]
    exact preimage_mem_irreducibleComponents hη j.isOpenEmbedding
      ⟨j p, subset_closure rfl, p, rfl⟩
  have hp' : p.asIdeal ∈ minimalPrimes _ := by
    rwa [← PrimeSpectrum.vanishingIdeal_singleton,
      PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
  let g := Limits.pullback.snd f j
  have : IsReduced (Limits.pullback f j) := isReduced_of_isOpenImmersion (Limits.pullback.fst f j)
  have : IsReduced (g.fiber p) := reduced_fiber_affine_base g p hp'
  let c : g.fiber p ⟶ f.fiber (j p) :=
    Limits.pullback.map _ _ _ _ (Limits.pullback.fst f j) (Spec.map (j.residueFieldMap p)) j
      Limits.pullback.condition.symm (by simp)
  have hc : IsPullback c (g.fiberToSpecResidueField p)
      (f.fiberToSpecResidueField (j p)) (Spec.map (j.residueFieldMap p)) :=
    isPullback_fiberToSpecResidueField_of_isPullback (.of_hasPullback f j) p
  have : IsIso c := hc.isIso_fst_of_isIso
  exact isReduced_of_isOpenImmersion (asIso c).inv

/-- Reduction commutes with taking a fibre at a generic point of an irreducible component.
The two equations identify the composite with the reduction inclusion as the canonical
map of fibres: its projections to `Z` and to `Spec κ(η)` are the prescribed ones.
No finite type, reducedness, or flatness assumptions are needed.

Source: Stacks Project, Tag 054Z, `lemma-reduction-generic-fibre`
(blueprint: lem-pur-reduction-generic-fibre).

Proof:
1. First treat a reduced affine source over an affine base. If p is the minimal prime
   corresponding to η, put L = (A ∖ p)⁻¹B. The fibre ring is L/(p A_p)L.
   The maximal ideal of A_p consists of nilpotents because A_p has dimension zero.
   Its image in the reduced localization L is therefore zero, so the fibre is reduced.
2. Pull back an affine cover of a reduced source to its fibre. Pullback pasting identifies
   each chart with the fibre of its affine chart, so step 1 proves reducedness over an
   affine base. Next choose an affine base chart containing η. Minimality is preserved
   by this open immersion, and its residue-field map is an isomorphism, identifying the
   old and new fibres. Thus every reduced scheme has reduced fibre over η.
3. The canonical map v : (Z_red)_η → Z_η is the base change of Z_red → Z; it is a
   surjective closed immersion. Its source is reduced by step 2. The universal property
   of reduction gives w : (Z_red)_η → (Z_η)_red with w followed by the reduction
   inclusion equal to v. Since v is a surjective closed immersion, so is w.
4. A surjective closed immersion into a reduced scheme is an isomorphism. Apply this to w.
   Pullback pasting gives the two required projection equations. The argument includes
   empty fibres and zero localizations, and uses no finiteness or flatness assumptions. -/
theorem Scheme.Hom.reduction_generic_fibre {Z T : Scheme.{u}} (h : Z ⟶ T)
    (η : T) (hη : closure ({η} : Set T) ∈ irreducibleComponents T) :
    ∃ e : (Z.nilradical.subschemeι ≫ h).fiber η ≅ (h.fiber η).nilradical.subscheme,
      e.hom ≫ (h.fiber η).nilradical.subschemeι ≫ h.fiberι η =
        (Z.nilradical.subschemeι ≫ h).fiberι η ≫ Z.nilradical.subschemeι ∧
      e.hom ≫ (h.fiber η).nilradical.subschemeι ≫ h.fiberToSpecResidueField η =
        (Z.nilradical.subschemeι ≫ h).fiberToSpecResidueField η := by
  have : IsReduced ((Z.nilradical.subschemeι ≫ h).fiber η) :=
    reduced_fiber_generic _ η hη
  let i := Z.nilradical.subschemeι
  have : Surjective i := ⟨Set.range_eq_univ.mp (by
    simp [i, Scheme.IdealSheafData.range_subschemeι, Z.support_nilradical])⟩
  let v : (i ≫ h).fiber η ⟶ h.fiber η :=
    (Limits.pullbackRightPullbackFstIso h (T.fromSpecResidueField η) i).inv ≫
      Limits.pullback.snd i (Limits.pullback.fst h (T.fromSpecResidueField η))
  have hv₁ : v ≫ h.fiberι η = (i ≫ h).fiberι η ≫ i := by
    simp [v, Scheme.Hom.fiberι]
  have hv₂ : v ≫ h.fiberToSpecResidueField η = (i ≫ h).fiberToSpecResidueField η := by
    simp [v, Scheme.Hom.fiberToSpecResidueField]
  have : IsClosedImmersion v := by dsimp [v]; infer_instance
  have : Surjective v := by dsimp [v]; infer_instance
  let w := v.liftNilradical
  have hw : w ≫ (h.fiber η).nilradical.subschemeι = v := by
    simp [w]
  have : IsClosedImmersion (w ≫ (h.fiber η).nilradical.subschemeι) := by
    rw [hw]; infer_instance
  have : IsClosedImmersion w := .of_comp w (h.fiber η).nilradical.subschemeι
  have : Surjective w := by
    constructor
    intro x
    obtain ⟨y, hy⟩ := v.surjective ((h.fiber η).nilradical.subschemeι x)
    refine ⟨y, (h.fiber η).nilradical.subschemeι.isEmbedding.injective ?_⟩
    simpa only [← Scheme.Hom.comp_apply, hw] using hy
  have : IsIso w := isIso_of_isClosedImmersion_of_surjective w
  refine ⟨asIso w, ?_, ?_⟩
  · change w ≫ _ ≫ _ = _
    rw [← Category.assoc, hw]
    exact hv₁
  · change w ≫ _ ≫ _ = _
    rw [← Category.assoc, hw]
    exact hv₂

end AlgebraicGeometry
