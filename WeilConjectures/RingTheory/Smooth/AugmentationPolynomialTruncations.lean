/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.RingTheory.Smooth.AugmentationPolynomialTruncationsSurjective
import WeilConjectures.RingTheory.Smooth.AugmentationPolynomialTruncationsInjective

/-!
# Propagation of first-order augmented polynomial coordinates

For a formally smooth augmented algebra, polynomial coordinates that are bijective to first
order are bijective modulo every power of the augmentation ideal.

## References

* [Stacks, Tag 05D5]
-/

@[expose] public section

universe u

namespace Algebra

/-- First-order polynomial coordinates of a formally smooth augmented algebra are
coordinates at every finite order: if `MvPolynomial (Fin n) B → C` induces a bijection modulo
the square of the augmentation ideal, it induces a bijection modulo every power of it. -/
theorem bijective_augmented_polynomial_truncations
    (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    [FormallySmooth B C] (ε : C →ₐ[B] B) (n : ℕ)
    (f : MvPolynomial (Fin n) B →ₐ[B] C)
    (hf : MvPolynomial.idealOfVars (Fin n) B ≤
      (RingHom.ker ε.toRingHom).comap f.toRingHom)
    (h₂ : Function.Bijective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ 2) f
        ((pow_le_pow_left' hf 2).trans (Ideal.le_comap_pow f.toRingHom 2)))) :
    ∀ k : ℕ, Function.Bijective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ k) f
        ((pow_le_pow_left' hf k).trans (Ideal.le_comap_pow f.toRingHom k))) := by
  intro k
  exact ⟨bijective_augmented_polynomial_truncations_injective B C ε n f hf h₂ k,
    bijective_augmented_polynomial_truncations_surjective B C ε n f hf h₂.2 k⟩

end Algebra
