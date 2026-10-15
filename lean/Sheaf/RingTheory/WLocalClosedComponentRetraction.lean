/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.ProEtale.WContractible

/-!
# Retractions from closed subsets of connected components

Source: Stacks Project, Tag 09AZ, proof of (3) implies (1), restriction to the closed
component subset (blueprint: lem-weil-pbc-wlocal-closed-component-retraction).
-/

@[expose] public section

universe u v

/-- A map of w-local rings identifying prime stalks and preserving closed points admits a
retraction whenever a closed subset of source-spectrum components maps bijectively onto the
target-spectrum components.

Source: Stacks Project, Tag 09AZ, proof of (3) implies (1).
(blueprint: lem-weil-pbc-wlocal-closed-component-retraction)

Proof: equip `S` with the `R`-algebra structure induced by `g` (def-weil-pbc-w-local).
The canonical map is then `g`. Its local ring maps are bijective by `hstalk`
(def-weil-pbc-localization-at-prime). The closed-point condition is `hclosed`.
Surjectivity of `hbij` gives a component in `T` over each component of `Spec R`, and
injectivity gives equality of two components of `T` with the same image. Apply the
closed-component restriction retraction theorem
(lem-weil-pbc-wlocal-isClosed-bijOn-retraction), obtaining `s` with `s.comp g = RingHom.id R`.
For different ring universes, carry out the same construction in their common maximum
universe by lifting the rings and transport the resulting retraction back. -/
theorem RingHom.exists_retraction_of_closed_component_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsWLocalRing R] [IsWLocalRing S] (g : R →+* S)
    (hstalk : g.BijectiveOnStalks)
    (hclosed : ∀ y ∈ closedPoints (PrimeSpectrum S),
      PrimeSpectrum.comap g y ∈ closedPoints (PrimeSpectrum R))
    (T : Set (ConnectedComponents (PrimeSpectrum S))) (hT : IsClosed T)
    (hbij : Function.Bijective
      (fun t : T ↦ (PrimeSpectrum.continuous_comap g).connectedComponentsMap t.val)) :
    ∃ s : S →+* R, s.comp g = RingHom.id R := by
  classical
  let eR : ULift.{v} R ≃+* R := ULift.ringEquiv
  let eS : ULift.{u} S ≃+* S := ULift.ringEquiv
  let pR := PrimeSpectrum.homeomorphOfRingEquiv eR
  let pS := PrimeSpectrum.homeomorphOfRingEquiv eS
  have hR : IsWLocalRing (ULift.{v} R) :=
    IsWLocalRing.of_surjective (f := eR.symm.toRingHom) eR.symm.surjective
  have hS : IsWLocalRing (ULift.{u} S) :=
    IsWLocalRing.of_surjective (f := eS.symm.toRingHom) eS.symm.surjective
  let cR := pR.continuous.connectedComponentsMap
  let cS := pS.continuous.connectedComponentsMap
  have hcR : Function.Bijective cR :=
    pR.isQuotientMap.isCoinducing.connectedComponentsMap_bijective (fun y ↦ by
      simpa using (isConnected_singleton (x := y)))
  have hcS : Function.Bijective cS :=
    pS.isQuotientMap.isCoinducing.connectedComponentsMap_bijective (fun y ↦ by
      simpa using (isConnected_singleton (x := y)))
  let T' := cS ⁻¹' T
  have hcomm : ∀ c,
      cR ((PrimeSpectrum.continuous_comap (RingHom.ulift.{v, u} g)).connectedComponentsMap c) =
        (PrimeSpectrum.continuous_comap g).connectedComponentsMap (cS c) := by
    intro c
    obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
    change ConnectedComponents.mk
      (PrimeSpectrum.comap eR.symm.toRingHom (PrimeSpectrum.comap (RingHom.ulift.{v, u} g) p)) =
      ConnectedComponents.mk
        (PrimeSpectrum.comap g (PrimeSpectrum.comap eS.symm.toRingHom p))
    congr 1
  let g' : ULift.{v} R →+* ULift.{u} S := RingHom.ulift g
  have hstalk' : g'.BijectiveOnStalks :=
    (eR.bijectiveOnStalks.comp hstalk).comp eS.symm.bijectiveOnStalks
  have hclosed' : ∀ y ∈ closedPoints (PrimeSpectrum (ULift.{u} S)),
      PrimeSpectrum.comap g' y ∈ closedPoints (PrimeSpectrum (ULift.{v} R)) := by
    intro y hy
    have hyS : pS y ∈ closedPoints (PrimeSpectrum S) := by
      apply mem_closedPoints_iff.mpr
      simpa only [Set.image_singleton] using
        pS.isClosedMap _ (mem_closedPoints_iff.mp hy)
    have hyR := hclosed (pS y) hyS
    apply mem_closedPoints_iff.mpr
    have hpre := (mem_closedPoints_iff.mp hyR).preimage pR.continuous
    have hpt : pR (PrimeSpectrum.comap (RingHom.ulift.{v, u} g) y) =
        PrimeSpectrum.comap g (pS y) := by
      change PrimeSpectrum.comap eR.symm.toRingHom
        (PrimeSpectrum.comap (RingHom.ulift.{v, u} g) y) =
          PrimeSpectrum.comap g (PrimeSpectrum.comap eS.symm.toRingHom y)
      rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
      rfl
    rw [← hpt] at hpre
    convert hpre using 1
    ext x
    simp [g']
  have hbij' : Function.Bijective
      (fun t : T' ↦ (PrimeSpectrum.continuous_comap g').connectedComponentsMap t.val) := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply hcS.1
      have heq := congrArg cR hab
      rw [hcomm, hcomm] at heq
      exact congrArg Subtype.val
        (hbij.1 (a₁ := ⟨cS a.val, a.property⟩) (a₂ := ⟨cS b.val, b.property⟩) heq)
    · intro c
      obtain ⟨t, ht⟩ := hbij.2 (cR c)
      obtain ⟨t', ht'⟩ := hcS.2 t.val
      refine ⟨⟨t', ?_⟩, hcR.1 ?_⟩
      · change cS t' ∈ T
        rw [ht']
        exact t.property
      · rw [hcomm, ht']
        exact ht
  let : Algebra (ULift.{v} R) (ULift.{u} S) := g'.toAlgebra
  obtain ⟨s', hs'⟩ :=
    exists_retraction_of_isClosed_of_bijOn (R := ULift.{v} R)
      (S := ULift.{u} S) hstalk' hclosed' T'
      (hT.preimage pS.continuous.connectedComponentsMap_continuous)
      (fun c ↦ by
        obtain ⟨t, ht⟩ := hbij'.2 c
        exact ⟨t.val, t.property, ht⟩)
      (fun t₁ ht₁ t₂ ht₂ h ↦ by
        have h' : (⟨t₁, ht₁⟩ : T') = ⟨t₂, ht₂⟩ := hbij'.1 h
        exact congrArg (fun t : T' ↦ t.val) h')
  refine ⟨eR.toRingHom.comp (s'.comp eS.symm.toRingHom), ?_⟩
  ext r
  exact congrArg ULift.down (RingHom.congr_fun hs' (ULift.up r))
