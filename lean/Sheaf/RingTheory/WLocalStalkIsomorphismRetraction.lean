/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import WeilConjectures.RingTheory.ProEtale.WLocal
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Topology.ExtremallyDisconnected
import Sheaf.RingTheory.ProfiniteComponentRingPullback
import Sheaf.RingTheory.WLocalClosedComponentRetraction

/-!
# Retractions of w-local maps identifying local rings

Source: Stacks Project, Tag 09AZ, `lemma-w-local-extremally-disconnected`,
proof of (3) implies (1)
(blueprint: lem-weil-pbc-wlocal-stalk-isomorphism-retraction).
-/

@[expose] public section

universe u v

namespace RingHom

/-- Continuous sections of surjections onto extremally disconnected compact Hausdorff spaces.
Source: Stacks Project, Tag 09AZ, via projectivity of extremally disconnected compact spaces.

Proof: transport the target and source along `Homeomorph.ulift` into common universes.
The transported target remains compact Hausdorff and extremally disconnected, so
`CompactT2.ExtremallyDisconnected.projective` lifts its identity map through the transported
surjection. Transport that lift back along the two homeomorphisms.
(blueprint: lem-weil-pbc-wlocal-stalk-isomorphism-retraction-section)
-/
theorem exists_continuous_section_of_surjective
    {α : Type u} {β : Type v} [TopologicalSpace α] [TopologicalSpace β]
    [CompactSpace α] [T2Space α] [ExtremallyDisconnected α]
    [CompactSpace β] [T2Space β]
    (f : β → α) (hf : Continuous f) (hs : Function.Surjective f) :
    ∃ ρ : α → β, Continuous ρ ∧ ∀ x, f (ρ x) = x := by
  let eα : ULift.{v} α ≃ₜ α := Homeomorph.ulift
  let eβ : ULift.{u} β ≃ₜ β := Homeomorph.ulift
  let F : ULift.{u} β → ULift.{v} α := eα.symm ∘ f ∘ eβ
  let _ : CompactSpace (ULift.{v} α) := eα.symm.compactSpace
  let _ : T2Space (ULift.{v} α) := eα.symm.t2Space
  let _ : ExtremallyDisconnected (ULift.{v} α) :=
    extremallyDisconnected_of_homeo eα.symm
  have hF : Continuous F := eα.symm.continuous.comp (hf.comp eβ.continuous)
  have hFs : Function.Surjective F := by
    intro x
    obtain ⟨y, hy⟩ := hs (eα x)
    refine ⟨eβ.symm y, ?_⟩
    simp [F, hy]
  obtain ⟨ρ', hρ'c, hρ'⟩ :=
    (CompactT2.ExtremallyDisconnected.projective
      (A := ULift.{v} α)) continuous_id hF hFs
  let ρ : α → β := eβ ∘ ρ' ∘ eα.symm
  refine ⟨ρ, eβ.continuous.comp (hρ'c.comp eα.symm.continuous), ?_⟩
  intro x
  have hx := congrFun hρ' (eα.symm x)
  change f (eβ (ρ' (eα.symm x))) = x
  change eα (F (ρ' (eα.symm x))) = x
  rw [show F (ρ' (eα.symm x)) = eα.symm x by
    simpa [Function.comp_apply] using hx]
  simp

/-- Stacks Project, Tag 09AZ, proof of (3) implies (1)
(blueprint: lem-weil-pbc-wlocal-stalk-isomorphism-retraction).
A faithfully flat map identifying all local rings has a retraction when its source
and target are w-local, its source component space is extremally disconnected, and
the closed-point loci are defined by an ideal and its extension.

Proof: faithful flatness makes the spectrum map surjective, hence also the induced
continuous map on connected components. The component spaces are compact Hausdorff
by `lem-weil-pbc-profinite-component-ring-pullback`. Projectivity of the extremally
disconnected target (`lem-weil-pbc-wlocal-stalk-isomorphism-retraction-section`)
gives a continuous section after lifting the spaces to common universes. Its image is
closed and maps bijectively to the source component space. The two zero-locus equalities
show that closed points contract to closed points. Apply
`lem-weil-pbc-wlocal-closed-component-retraction` to this image,
using the assumed bijectivity of every canonical localization map, to obtain the
ring retraction. Spectrum surjectivity is
`lem-weil-pbc-faithfully-flat-surjective-spectrum`. -/
theorem exists_retraction_of_wLocal_stalk_isomorphisms
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (g : R →+* S) (hg : g.FaithfullyFlat) [IsWLocalRing R] [IsWLocalRing S]
    [ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum R))]
    (I : Ideal R)
    (hI : PrimeSpectrum.zeroLocus (I : Set R) = closedPoints (PrimeSpectrum R))
    (hIS : PrimeSpectrum.zeroLocus (I.map g : Set S) = closedPoints (PrimeSpectrum S))
    (hlocal : ∀ (q : Ideal S) [q.IsPrime],
      Function.Bijective (Localization.localRingHom (q.comap g) q g rfl)) :
    ∃ s : S →+* R, s.comp g = RingHom.id R := by
  let _ : Algebra R S := g.toAlgebra
  have : Module.FaithfullyFlat R S :=
    RingHom.faithfullyFlat_algebraMap_iff.mp (show (algebraMap R S).FaithfullyFlat from hg)
  have hstalk : g.BijectiveOnStalks := by
    intro q hq
    exact hlocal q
  have hclosed : ∀ y ∈ closedPoints (PrimeSpectrum S),
      PrimeSpectrum.comap g y ∈ closedPoints (PrimeSpectrum R) := by
    intro y hy
    rw [← hIS, PrimeSpectrum.mem_zeroLocus] at hy
    rw [← hI, PrimeSpectrum.mem_zeroLocus]
    intro a ha
    exact Ideal.mem_comap.mpr (hy (Ideal.mem_map_of_mem g ha))
  have hR := Algebra.exists_profinite_component_ring_pullback R
  let _ : CompactSpace (ConnectedComponents (PrimeSpectrum R)) := hR.1
  let _ : T2Space (ConnectedComponents (PrimeSpectrum R)) := hR.2.1
  have hS := Algebra.exists_profinite_component_ring_pullback S
  let _ : CompactSpace (ConnectedComponents (PrimeSpectrum S)) := hS.1
  let _ : T2Space (ConnectedComponents (PrimeSpectrum S)) := hS.2.1
  let f : ConnectedComponents (PrimeSpectrum S) →
      ConnectedComponents (PrimeSpectrum R) :=
    (PrimeSpectrum.continuous_comap g).connectedComponentsMap
  have hfcont : Continuous f :=
    (PrimeSpectrum.continuous_comap g).connectedComponentsMap_continuous
  have hfsurj : Function.Surjective f := by
    exact (PrimeSpectrum.continuous_comap g).connectedComponentsMap_surjective
      (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hg).2
  obtain ⟨ρ, hρcont, hρ⟩ :=
    exists_continuous_section_of_surjective f hfcont hfsurj
  refine RingHom.exists_retraction_of_closed_component_bijective g hstalk hclosed
    (Set.range ρ) (isCompact_range hρcont).isClosed ?_
  constructor
  · intro t₁ t₂ ht
    apply Subtype.ext
    obtain ⟨c₁, hc₁⟩ := t₁.property
    obtain ⟨c₂, hc₂⟩ := t₂.property
    have hcc : c₁ = c₂ := by
      have h := ht
      change f t₁.val = f t₂.val at h
      rw [← hc₁, ← hc₂, hρ c₁, hρ c₂] at h
      exact h
    rw [← hc₁, ← hc₂, hcc]
  · intro c
    exact ⟨⟨ρ c, Set.mem_range_self c⟩, hρ c⟩

end RingHom
