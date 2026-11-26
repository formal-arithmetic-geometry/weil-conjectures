/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Prime membership in a finite free module after localization

Membership in `p R^n` is coordinatewise membership in `p`, and it is detected after localizing
at the prime `p`.

## Implementation details

Localization commutes with ideal scalar products, so membership of `s / 1` in `p (R^n)_p` yields
`t s ∈ p R^n` for some `t ∉ p`; primality then puts every coordinate of `s` in `p`.

## References

* [Stacks, Tags 00CO, 07JZ, 00NX]
-/

@[expose] public section

universe u

namespace Module

/-- Prime membership in `R^n` is detected after localization at the same prime, and each
coordinate satisfies the corresponding scalar criterion: for `s : Fin n → R`, the image of `s`
in `(R^n)_p` lies in `p (R^n)_p` iff `s ∈ p R^n`, and `s_i / 1 ∈ p R_p` iff `s_i ∈ p`.
-/
theorem free_prime_mem_localized_iff
    {R : Type u} [CommRing R] (n : ℕ) (s : Fin n → R) (p : Ideal R) [p.IsPrime] :
    (LocalizedModule.mkLinearMap p.primeCompl (Fin n → R) s ∈
        (Ideal.map (algebraMap R (Localization.AtPrime p)) p) •
          (⊤ : Submodule (Localization.AtPrime p)
            (LocalizedModule p.primeCompl (Fin n → R))) ↔
      s ∈ p • (⊤ : Submodule R (Fin n → R))) ∧
    (∀ i : Fin n,
      algebraMap R (Localization.AtPrime p) (s i) ∈
          Ideal.map (algebraMap R (Localization.AtPrime p)) p ↔ s i ∈ p) := by
  have hcoord (v : Fin n → R) :
      v ∈ p • (⊤ : Submodule R (Fin n → R)) ↔ ∀ i, v i ∈ p := by
    constructor
    · intro hv
      refine Submodule.smul_induction_on hv ?_ ?_
      · intro r hr w _ i
        exact p.mul_mem_right (w i) hr
      · intro v w hv hw i
        exact p.add_mem (hv i) (hw i)
    · intro hv
      rw [pi_eq_sum_univ' v]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem_smul (hv i) Submodule.mem_top
  let f := LocalizedModule.mkLinearMap p.primeCompl (Fin n → R)
  have hloc : (p • (⊤ : Submodule R (Fin n → R))).localized'
      (Localization.AtPrime p) p.primeCompl f =
        Ideal.map (algebraMap R (Localization.AtPrime p)) p • ⊤ := by
    rw [Submodule.localized'_smul, Ideal.localized'_eq_map, Submodule.localized'_top]
  constructor
  · rw [← hloc, Submodule.mem_localized']
    constructor
    · rintro ⟨v, hv, t, ht⟩
      have he : IsLocalizedModule.mk' f v t = IsLocalizedModule.mk' f s (1 : p.primeCompl) := by
        simpa only [IsLocalizedModule.mk'_one] using ht
      obtain ⟨a, ha⟩ := (IsLocalizedModule.mk'_eq_mk'_iff f v s t 1).mp he
      simp only [one_smul] at ha
      have hs : (a * t) • s ∈ p • (⊤ : Submodule R (Fin n → R)) := by
        rw [mul_smul, ha]
        exact Submodule.smul_of_tower_mem _ a hv
      apply (hcoord s).mpr
      intro i
      have hi := (hcoord _).mp hs i
      change ((a * t : p.primeCompl) : R) * s i ∈ p at hi
      exact (Ideal.IsPrime.mem_or_mem (inferInstance : p.IsPrime) hi).resolve_left (a * t).property
    · intro hs
      exact ⟨s, hs, 1, IsLocalizedModule.mk'_one p.primeCompl f s⟩
  · intro i
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl]
    constructor
    · rintro ⟨u, hu, hus⟩
      rcases Ideal.IsPrime.mem_or_mem (inferInstance : p.IsPrime) hus with hu' | hi
      · exact False.elim (hu hu')
      · exact hi
    · intro hi
      exact ⟨1, p.primeCompl.one_mem, by simpa using hi⟩

end Module
