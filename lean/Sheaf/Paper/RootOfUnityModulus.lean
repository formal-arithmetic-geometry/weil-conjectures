/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra

/-!
# Modulus and weight of a root of unity

Source: blueprint main-20261015, sec-purity-real-sheaves, sk-p-real-rankone,
lemma lem-tw-root-of-unity-modulus (blueprint: lem-tw-root-of-unity-modulus).

The absolute value is the complex norm through the fixed field isomorphism, as in
`def-tw-eigenvalue`; it is not the ell-adic norm on the coefficient field.
-/

@[expose] public section

set_option autoImplicit false

namespace AlgebraicGeometry.WeilGroup

/-- Every root of unity has absolute value one and weight zero, and its image under
any field isomorphism to the complex numbers has modulus one.

Source: blueprint main-20261015, sec-purity-real-sheaves, sk-p-real-rankone,
lemma lem-tw-root-of-unity-modulus (blueprint: lem-tw-root-of-unity-modulus).
The primes `p`, `l`, exponent `r`, and base `p ^ r` retain the ambient conventions of
`def-tw-eigenvalue`. The fixed `ι` has no continuity requirement.

Proof: choose `n ≥ 1` with `ζ ^ n = 1`. A field isomorphism preserves powers and one,
so `(ι ζ) ^ n = 1`. Since `n ≠ 0`, `Complex.norm_eq_one_of_pow_eq_one`
(lem-tw-complex-norm-root-of-unity) gives `‖ι ζ‖ = 1`. This is the absolute value
of def-tw-eigenvalue. Its weight condition is `IsOfWeight`, and at weight zero its
right side is `(p ^ r : ℝ) ^ (0 / 2) = 1`. Applying the same argument to any other
field isomorphism `κ` gives the last clause. -/
theorem rootOfUnity_modulus_and_isOfWeight_zero
    (p l r : ℕ) [Fact p.Prime] [Fact l.Prime] (_hr : 1 ≤ r) (_hlp : l ≠ p)
    (ι : PadicAlgCl l ≃+* ℂ) (ζ : (PadicAlgCl l)ˣ)
    (hζ : ∃ n : ℕ, 1 ≤ n ∧ ζ ^ n = 1) :
    ‖ι (ζ : PadicAlgCl l)‖ = 1 ∧
      IsOfWeight ι.toRingHom (p ^ r) 0 (ζ : PadicAlgCl l) ∧
      ∀ κ : PadicAlgCl l ≃+* ℂ, ‖κ (ζ : PadicAlgCl l)‖ = 1 := by
  obtain ⟨n, hn, hζ⟩ := hζ
  have hpow : (ζ : PadicAlgCl l) ^ n = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hζ
  have hnorm (κ : PadicAlgCl l ≃+* ℂ) : ‖κ (ζ : PadicAlgCl l)‖ = 1 := by
    apply Complex.norm_eq_one_of_pow_eq_one (n := n)
    · rw [← map_pow, hpow, map_one]
    · exact Nat.ne_of_gt hn
  refine ⟨hnorm ι, ?_, hnorm⟩
  rw [IsOfWeight, zero_div, Real.rpow_zero]
  exact hnorm ι

end AlgebraicGeometry.WeilGroup
