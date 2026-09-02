/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Complements on residue fields of local rings

## Main results

- `IsLocalRing.exists_comp_eq_residue_comp`: if `π : P →+* K` is surjective and
  `ρ : P →+* V` maps `RingHom.ker π` into the maximal ideal of a local ring `V`, then the
  residue map of `ρ` factors through `π`.
- `IsLocalRing.ResidueField.map_surjective`: a surjective local homomorphism induces a
  surjection on residue fields.
-/

@[expose] public section

namespace IsLocalRing

/-- If `π : P →+* K` is surjective and `ρ : P →+* V` carries `RingHom.ker π` into the
maximal ideal of the local ring `V`, then `residue V ∘ ρ` factors through `π`. -/
theorem exists_comp_eq_residue_comp {P K V : Type*} [CommRing P] [CommRing K] [CommRing V]
    [IsLocalRing V] {π : P →+* K} (hπ : Function.Surjective π) (ρ : P →+* V)
    (hker : ∀ a ∈ RingHom.ker π, ρ a ∈ maximalIdeal V) :
    ∃ τ : K →+* ResidueField V, τ.comp π = (residue V).comp ρ := by
  refine ⟨(Ideal.Quotient.lift (RingHom.ker π) ((residue V).comp ρ) fun a ha ↦
      Ideal.Quotient.eq_zero_iff_mem.mpr (hker a ha)).comp
    ((RingHom.quotientKerEquivOfSurjective hπ).symm : K →+* P ⧸ RingHom.ker π), ?_⟩
  refine RingHom.ext fun a ↦ ?_
  have hmk : ((RingHom.quotientKerEquivOfSurjective hπ).symm : K →+* P ⧸ RingHom.ker π) (π a) =
      Ideal.Quotient.mk (RingHom.ker π) a := by
    apply (RingHom.quotientKerEquivOfSurjective hπ).injective
    rw [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    exact (RingHom.kerLift_mk π a).symm
  simp only [RingHom.comp_apply]
  rw [hmk, Ideal.Quotient.lift_mk, RingHom.comp_apply]

/-- A surjective local homomorphism of local rings induces a surjection on residue
fields. -/
lemma ResidueField.map_surjective {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (hf : Function.Surjective f) :
    Function.Surjective (ResidueField.map f) := by
  intro y
  obtain ⟨s, rfl⟩ := residue_surjective y
  obtain ⟨r, rfl⟩ := hf s
  exact ⟨residue R r, map_residue f r⟩

end IsLocalRing
