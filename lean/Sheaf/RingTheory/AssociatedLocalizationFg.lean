/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Descent of an annihilator from localization at a finitely generated prime

Source: Stacks Project, Algebra, Tag 0310 (2), used in Tag 058A
(blueprint: lem-sc-associated-localization-fg).
-/

@[expose] public section

universe u v

namespace Module

/-- If the maximal ideal of `Rₚ` is the annihilator of an element of `Mₚ`, and `p` is
finitely generated, then `p` is the annihilator of an element of `M`.
Source: Stacks Project, Algebra, Tag 0310 (2), used in Tag 058A
(blueprint: lem-sc-associated-localization-fg).

Proof (using def-weil-pbc-localization-at-prime and def-weil-pbc-module-localization):
1. Write the localized element as `m/s` and `p = (f₁, ..., fₙ)`. If `a` annihilates `m`,
then `a/1` annihilates `m/s`. Contracting the maximal ideal of `Rₚ` gives `p`, so
`Ann_R(m) ⊆ p`.
2. For each generator `fᵢ`, clear a denominator to obtain `uᵢ ∉ p` with `uᵢ fᵢ m = 0`.
Set `u = ∏ uᵢ` and `m' = u m`. Every generator kills `m'`, and `u ∉ p`. Also `m' ≠ 0`,
since otherwise the unit `u/1` would annihilate `m/s`.
3. Thus `p ⊆ Ann_R(m')`. Conversely, if `a m' = 0`, then `au ∈ Ann_R(m) ⊆ p`.
Primality and `u ∉ p` imply `a ∈ p`, proving `Ann_R(m') = p`. -/
theorem exists_annihilator_eq_of_localization_atPrime
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (p : Ideal R) [p.IsPrime] (hp : p.FG)
    (h : ∃ z : LocalizedModule.AtPrime p M,
      IsLocalRing.maximalIdeal (Localization.AtPrime p) =
        (⊥ : Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).colon {z}) :
    ∃ m : M, p = (⊥ : Submodule R M).colon {m} := by
  classical
  let f := LocalizedModule.mkLinearMap p.primeCompl M
  obtain ⟨z, hz⟩ := h
  obtain ⟨T, hT⟩ := hp
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p.primeCompl f z
  simp only [Function.uncurry_apply_pair] at hz
  have hcontract :
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)).comap
        (algebraMap R (Localization.AtPrime p)) = p :=
    Localization.AtPrime.under_maximalIdeal (I := p)
  have mem (a : T) :
      algebraMap R (Localization.AtPrime p) a ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    rw [← Ideal.mem_comap, hcontract]
    rw [← hT]
    exact Ideal.subset_span a.2
  simp only [hz, Submodule.mem_colon_singleton, Submodule.mem_bot,
    algebraMap_smul, ← IsLocalizedModule.mk'_smul,
    IsLocalizedModule.mk'_eq_zero' f] at mem
  choose g hg using mem
  refine ⟨(∏ a, g a).1 • m, le_antisymm ?_ ?_⟩
  · apply hT ▸ Ideal.span_le.mpr
    intro a ha
    simp only [SetLike.mem_coe, Submodule.mem_colon_singleton, Submodule.mem_bot]
    obtain ⟨u, hu⟩ : g ⟨a, ha⟩ ∣ (∏ a, g a) :=
      Finset.dvd_prod_of_mem g (Finset.mem_univ (⟨a, ha⟩ : T))
    rw [hu, Submonoid.coe_mul, smul_smul, ← mul_assoc, mul_comm,
      ← smul_smul, mul_comm, ← smul_smul]
    exact smul_eq_zero_of_right u.1 (hg ⟨a, ha⟩)
  · intro r hr
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_smul] at hr
    have hru : r * (∏ a, g a).1 ∈ p := by
      have hmem : algebraMap R (Localization.AtPrime p) (r * (∏ a, g a).1) ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
        rw [hz, Submodule.mem_colon_singleton, algebraMap_smul,
          ← IsLocalizedModule.mk'_smul, hr, IsLocalizedModule.mk'_zero]
        exact Submodule.zero_mem _
      change r * (∏ a, g a).1 ∈
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)).comap
          (algebraMap R (Localization.AtPrime p)) at hmem
      exact (le_of_eq hcontract) hmem
    exact (‹p.IsPrime›.mul_mem_iff_mem_or_mem.mp hru).resolve_right (∏ a, g a).2

end Module
