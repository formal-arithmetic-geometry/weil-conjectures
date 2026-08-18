/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Descending a field point to the residue field of a local ring

If `π : P ↠ K` is a surjective ring homomorphism onto a field and `ρ : P →+* A` is a
ring homomorphism into a local ring carrying `ker π` into the maximal ideal, then the
residue map of `A` factors through `π`
(`IsLocalRing.exists_ringHom_residue_comp_of_surjective`). This is the descent step of
the Stacks Project proof of Tag 0894.
-/

@[expose] public section

universe u

namespace IsLocalRing

open IsLocalRing

variable {P K A : Type u} [CommRing P] [Field K] [CommRing A] [IsLocalRing A]

/-- **Descent of a surjection onto a field along a residue map**: if `π : P →+* K` is
surjective onto a field and `ρ : P →+* A` maps `ker π` into the maximal ideal of the
local ring `A`, then there is a (unique) `τ : K →+* ResidueField A` with
`τ ∘ π = residue A ∘ ρ`. -/
theorem exists_ringHom_residue_comp_of_surjective {π : P →+* K}
    (hπ : Function.Surjective π) (ρ : P →+* A)
    (hker : ∀ a ∈ RingHom.ker π, ρ a ∈ maximalIdeal A) :
    ∃ τ : K →+* ResidueField A, τ.comp π = (residue A).comp ρ := by
  have hvanish : ∀ a ∈ RingHom.ker π, ((residue A).comp ρ) a = 0 := fun a ha ↦ by
    rw [RingHom.comp_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker a ha)
  set L : (P ⧸ RingHom.ker π) →+* ResidueField A :=
    Ideal.Quotient.lift (RingHom.ker π) ((residue A).comp ρ) hvanish with hL
  refine ⟨L.comp ((RingHom.quotientKerEquivOfSurjective hπ).symm :
    K →+* P ⧸ RingHom.ker π), RingHom.ext fun a ↦ ?_⟩
  have h1 : (RingHom.quotientKerEquivOfSurjective hπ).symm (π a) =
      Ideal.Quotient.mk (RingHom.ker π) a := by
    apply (RingHom.quotientKerEquivOfSurjective hπ).injective
    rw [RingEquiv.apply_symm_apply]
    exact (RingHom.kerLift_mk π a).symm
  change L ((RingHom.quotientKerEquivOfSurjective hπ).symm (π a)) = _
  rw [h1, hL, Ideal.Quotient.lift_mk]

end IsLocalRing
