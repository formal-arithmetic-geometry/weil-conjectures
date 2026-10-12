/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Finiteness.Defs
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
  sorry

end Ideal
