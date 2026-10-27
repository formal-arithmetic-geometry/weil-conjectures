/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Ideal
import Sheaf.RingTheory.AssociatedLocalizationFg
import Sheaf.RingTheory.WeakAssLocalization

/-!
# Associated and weakly associated finitely generated primes

Source: Stacks Project, Algebra, Lemma 10.66.9, Tag 058A
(blueprint: lem-sc-ass-weakass-fg-prime).

Association here means equality with an element's annihilator, rather than equality with its
radical as in Mathlib's `IsAssociatedPrime`. Weak association means membership in the minimal
primes over that annihilator. Both notions are written using Mathlib's existing ideal operations.
-/

@[expose] public section

universe u v

namespace Ideal

private theorem exists_annihilator_eq_maximal_of_radical
    {A : Type*} [CommRing A] [IsLocalRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (hfg : (IsLocalRing.maximalIdeal A).FG) (x : N)
    (hx : ((⊥ : Submodule A N).colon {x}).radical = IsLocalRing.maximalIdeal A) :
    ∃ y : N, IsLocalRing.maximalIdeal A = (⊥ : Submodule A N).colon {y} := by
  classical
  let q := IsLocalRing.maximalIdeal A
  let I := (⊥ : Submodule A N).colon {x}
  have hex : ∃ n : ℕ, q ^ n ≤ I :=
    Ideal.exists_pow_le_of_le_radical_of_fg (le_of_eq hx.symm) hfg
  let n := Nat.find hex
  have hn : q ^ n ≤ I := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h
    have htop : I = ⊤ := top_unique (by simpa [h] using hn)
    have hx' : I.radical = q := hx
    have : q = ⊤ := by simpa [htop, Ideal.radical_top] using hx'.symm
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top this
  have hprev : ¬ q ^ (n - 1) ≤ I := Nat.find_min hex (by omega)
  obtain ⟨r, hr, hri⟩ := SetLike.not_le_iff_exists.mp hprev
  have hy : r • x ≠ 0 := by
    simpa only [I, Submodule.mem_colon_singleton, Submodule.mem_bot] using hri
  refine ⟨r • x, le_antisymm ?_ ?_⟩
  · intro a ha
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_smul]
    have har : a * r ∈ q ^ n := by
      have := Ideal.mul_mem_mul (show a ∈ q from ha) hr
      simpa [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)] using this
    simpa only [I, Submodule.mem_colon_singleton, Submodule.mem_bot] using hn har
  · apply IsLocalRing.le_maximalIdeal
    intro htop
    apply hy
    have hone : (1 : A) ∈ (⊥ : Submodule A N).colon {r • x} := by rw [htop]; trivial
    simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot, one_smul] using hone

/-- Source: Stacks Project, Algebra, Lemma 10.66.9, Tag 058A
(blueprint: lem-sc-ass-weakass-fg-prime). A finitely generated prime is the annihilator of an
element exactly when it is minimal over an element's annihilator.

Proof: If `p` is an element's annihilator, its primality makes it minimal over that same ideal.
Conversely, `lem-sc-weakass-localization` (Tag 0566) gives an element of `M_p` whose annihilator
has radical `p R_p`. Write `p = (g_1, ..., g_n)`. Each generator has a least positive exponent
killing this element. Choose an element with this radical for which the sum of these exponents
is minimal. If an exponent `e_i` exceeds one, replace the element by `g_i^(e_i-1)` times it.
This is nonzero and still has annihilator with radical `p R_p`: powers of all generators kill
it, and its proper annihilator is contained in the maximal ideal `p R_p`. Its exponent sum is
smaller, a contradiction. All exponents are therefore one, so its annihilator is exactly
`p R_p`. Finally `lem-sc-associated-localization-fg` (Tag 0310) descends this associated prime
because `p` is finitely generated, giving an element of `M` with annihilator `p`. -/
theorem annihilator_eq_iff_mem_minimalPrimes_of_fg
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (p : Ideal R) (hp : p.IsPrime) (hfg : p.FG) :
    (∃ m : M, p = (⊥ : Submodule R M).colon {m}) ↔
      ∃ m : M, p ∈ ((⊥ : Submodule R M).colon {m}).minimalPrimes := by
  let : p.IsPrime := hp
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [← hm, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton p
  · intro h
    obtain ⟨x, hx⟩ := (Module.weakly_associated_atPrime_iff (M := M) p).2.mp
      ((Module.weakly_associated_atPrime_iff (M := M) p).1.mp h)
    apply Module.exists_annihilator_eq_of_localization_atPrime p hfg
    have hmap := IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)
    have hfg' : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).FG := by
      rw [← hmap]
      exact hfg.map _
    exact exists_annihilator_eq_maximal_of_radical hfg' x (hx.trans hmap)

end Ideal
