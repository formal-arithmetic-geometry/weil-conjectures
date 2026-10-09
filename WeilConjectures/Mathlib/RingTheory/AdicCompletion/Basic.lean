/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Nakayama

/-!
# Finite modules over an adically complete ring

Over a ring `R` complete for an ideal `I`, a module which is finite as a set is killed by a
power of `I`: the powers `I ^ k • M` form a decreasing chain of submodules of the finite module
`M`, which stabilizes at some `N` with `I • N = N`, and `N = 0` by Nakayama's lemma since `I` lies
in the Jacobson radical.

## Main statements

- `IsAdicComplete.exists_pow_smul_top_eq_bot`: a finite `R`-module is killed by a power of `I`.
-/

@[expose] public section

namespace IsAdicComplete

variable {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
  (M : Type*) [AddCommGroup M] [Module R M] [Finite M]

/-- Over a ring complete for an ideal `I`, a module which is finite as a set is killed by a power
of `I`. -/
theorem exists_pow_smul_top_eq_bot : ∃ k : ℕ, I ^ k • (⊤ : Submodule R M) = ⊥ := by
  have := isArtinian_of_finite (R := R) (M := M)
  let f : ℕ →o (Submodule R M)ᵒᵈ :=
    ⟨fun k ↦ OrderDual.toDual (I ^ k • ⊤), fun a b hab ↦
      Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes f
  have hfg : (I ^ n • (⊤ : Submodule R M)).FG := by
    have : Module.Finite R ↥(I ^ n • (⊤ : Submodule R M)) := Module.Finite.of_finite
    exact Submodule.FG.of_finite
  refine ⟨n, Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I _ hfg ?_ (le_jacobson_bot I)⟩
  have h : I ^ n • (⊤ : Submodule R M) = I ^ (n + 1) • ⊤ :=
    congrArg OrderDual.ofDual (hn (n + 1) (Nat.le_succ n))
  rw [pow_succ', Submodule.mul_smul] at h
  exact h.le

end IsAdicComplete
