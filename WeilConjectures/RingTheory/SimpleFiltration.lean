/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Length

/-!
# Simple filtrations of finite-length modules

A module of finite length admits a finite strictly increasing filtration with simple
successive quotients.

## References

* [Stacks, Tag 02LY]
* [Stacks, Tag 00J1]
* [Stacks, Tag 00J3], part (2)
-/

@[expose] public section

universe u v

namespace Module

/-- A finite-length module admits a finite strictly increasing filtration with simple quotients.
-/
theorem exists_simple_filtration_of_length_lt_top
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (hM : Module.length R M < ⊤) :
    ∃ (r : ℕ) (F : Fin (r + 1) → Submodule R M),
      F 0 = ⊥ ∧ F (Fin.last r) = ⊤ ∧
        (∀ i : Fin r, F i.castSucc < F i.succ) ∧
        (∀ i : Fin r,
          IsSimpleModule R
            (↥(F i.succ) ⧸ Submodule.comap (F i.succ).subtype (F i.castSucc))) := by
  obtain ⟨s, hs₀, hs₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp
    (Module.length_ne_top_iff.mp hM.ne)
  refine ⟨s.length, s, hs₀, hs₁, ?_, ?_⟩
  · intro i
    exact (s.step i).lt
  · intro i
    exact (covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)

end Module
