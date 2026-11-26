/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Nakayama's lemma for a nilpotent ideal

If `I` is a nilpotent ideal and `u : N → M` is surjective modulo `I`, then `u` is surjective.

## Implementation details

If `Q = I • Q` then `Q = I^n • Q = 0` for large `n`; applied to `M / range u` this shows
`range u = ⊤`.

## References

* [Stacks, Tag 00DV] (parts (9)–(11))
-/

@[expose] public section

universe u v w

namespace RingTheory

/-- Let `R` be a commutative ring, `I` a nilpotent ideal, and `u : N →ₗ[R] M` a
linear map. If the induced map `N/IN → M/IM` (`Submodule.mapQ` on the quotients by
`I • ⊤`) is surjective, then `u` is surjective.
-/
theorem surjective_of_surjective_mod_nilpotent
    (R : Type u) [CommRing R] (N : Type v) (M : Type w)
    [AddCommGroup N] [AddCommGroup M] [Module R N] [Module R M]
    (I : Ideal R) (u : N →ₗ[R] M)
    (hI : ∃ k : ℕ, 0 < k ∧ I ^ k = ⊥)
    (h : Function.Surjective ((I • ⊤ : Submodule R N).mapQ (I • ⊤ : Submodule R M) u
      (Submodule.smul_top_le_comap_smul_top I u))) :
    Function.Surjective u := by
  have hrange : (I • ⊤ : Submodule R M) ⊔ u.range = ⊤ := by
    apply (Submodule.map_mkQ_eq_top _ _).mp
    rw [← Submodule.range_mapQ (I • ⊤ : Submodule R N)
      (I • ⊤ : Submodule R M) u (Submodule.smul_top_le_comap_smul_top I u)]
    exact LinearMap.range_eq_top.mpr h
  have hpow : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R M) ⊔ u.range = ⊤ := by
    intro n
    induction n with
    | zero => simp [Ideal.one_eq_top]
    | succ n ih =>
      calc
        (I ^ (n + 1) • ⊤ : Submodule R M) ⊔ u.range =
            I ^ n • (I • ⊤ : Submodule R M) ⊔ u.range := by
          rw [pow_succ, Submodule.mul_smul]
        _ = I ^ n • ((I • ⊤ : Submodule R M) ⊔ u.range) ⊔ u.range := by
          rw [Submodule.smul_sup, sup_assoc,
            sup_of_le_right (Submodule.smul_le_right (I := I ^ n) (N := u.range))]
        _ = (I ^ n • ⊤ : Submodule R M) ⊔ u.range := by rw [hrange]
        _ = ⊤ := ih
  obtain ⟨k, _, hk⟩ := hI
  apply LinearMap.range_eq_top.mp
  simpa [hk] using hpow k

end RingTheory
