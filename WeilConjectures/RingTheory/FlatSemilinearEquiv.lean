/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness under a simultaneous change of rings and modules

Flatness is preserved when both the ring and the module are replaced by equivalent ones,
compatibly with the scalar actions.

## Implementation details

The module `N` is regarded as an `R`-module by restriction along the ring equivalence; the
additive equivalence then becomes `R`-linear, and flatness over `R` and over `S` are compared via
the flat ring maps `R → S` and `S → R`.

## References

* [Stacks, Tag 02JO]
-/

@[expose] public section

namespace Module.Flat

/-- Flatness is invariant under compatible ring and additive equivalences: if `eM` is
`eR`-semilinear, then `M` is flat over `R` if and only if `N` is flat over `S`. -/
theorem semilinearEquiv_iff
    {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (eR : R ≃+* S) (eM : M ≃+ N)
    (h : ∀ r m, eM (r • m) = eR r • eM m) : Flat R M ↔ Flat S N := by
  let : Algebra R S := eR.toRingHom.toAlgebra
  let : Module R N := Module.compHom N eR.toRingHom
  let e : M ≃ₗ[R] N := { eM with map_smul' := h }
  rw [equiv_iff e]
  constructor
  · intro hN
    let : Algebra S R := eR.symm.toRingHom.toAlgebra
    let : Flat R N := hN
    let : Flat S R := RingHom.Flat.of_bijective eR.symm.bijective
    let : IsScalarTower S R N := ⟨fun s r n ↦ by
      change eR (eR.symm s * r) • n = s • (eR r • n)
      rw [map_mul, eR.apply_symm_apply, mul_smul]⟩
    exact trans S R N
  · intro hN
    let : Flat S N := hN
    let : Flat R S := RingHom.Flat.of_bijective eR.bijective
    let : IsScalarTower R S N := ⟨fun r s n ↦ by
      change (eR r * s) • n = eR r • (s • n)
      exact mul_smul _ _ _⟩
    exact trans R S N

end Module.Flat
