/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite free resolutions over Noetherian rings

Every finite module over a Noetherian ring admits a resolution by finite free modules.

## Implementation details

Choose a finite free surjection onto `M`, then repeatedly cover the (finitely generated) kernel
of the last map by a finite free module; the construction is a recursion on the degree.

## References

* [Stacks, Tag 00LP] (2)
-/

@[expose] public section

universe u v

namespace Module

/-- Every finite module over a (left) Noetherian ring admits an infinite resolution
by finite free modules. Here `Fin (n i) → R` represents `R^{⊕ nᵢ}` and `d i` maps the free
term of degree `i + 1` to that of degree `i`. -/
theorem exists_finite_free_resolution
    (R : Type u) [Ring R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (n : ℕ → ℕ) (ε : (Fin (n 0) → R) →ₗ[R] M)
      (d : ∀ i : ℕ, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R)),
      Function.Surjective ε ∧ LinearMap.ker ε = LinearMap.range (d 0) ∧
        ∀ i : ℕ, LinearMap.ker (d i) = LinearMap.range (d (i + 1)) := by
  classical
  obtain ⟨n₀, ε, hε⟩ := Module.Finite.exists_fin' R M
  have covers (n : ℕ) (K : Submodule R (Fin n → R)) :
      ∃ (m : ℕ) (f : (Fin m → R) →ₗ[R] (Fin n → R)), LinearMap.range f = K := by
    exact (Submodule.fg_iff_exists_fin_linearMap R (Fin n → R)).mp
      (Submodule.FG.of_le Module.Finite.fg_top le_top)
  -- A state records a finite free term and the kernel to be covered next.
  choose rank map range_map using covers
  let next : (Σ n : ℕ, Submodule R (Fin n → R)) →
      (Σ n : ℕ, Submodule R (Fin n → R)) :=
    fun s ↦ ⟨rank s.1 s.2, LinearMap.ker (map s.1 s.2)⟩
  -- The successor stores precisely the kernel of the map just chosen.
  let s : ℕ → Σ n : ℕ, Submodule R (Fin n → R) :=
    Nat.rec ⟨n₀, LinearMap.ker ε⟩ (fun _ t ↦ next t)
  refine ⟨fun i ↦ (s i).1, ε, fun i ↦ map (s i).1 (s i).2, hε, ?_, ?_⟩
  · exact (range_map n₀ (LinearMap.ker ε)).symm
  · intro i
    exact (range_map (s (i + 1)).1 (s (i + 1)).2).symm

end Module
