/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.RingTheory.WeaklyAssociated
public import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Weakly associated primes and zero-divisors

Source: Stacks Project, Algebra, Lemma 10.66.7 (Tag 05C3)
(blueprint: lem-sc-affine-weakass-nonzerodivisors).
-/

@[expose] public section

universe v

namespace Ideal

/-- In a commutative ring, the union of weakly associated primes is exactly
the set of zero-divisors, and its complement is the set of non-zero-divisors.
This is Stacks Project, Algebra, Lemma 10.66.7 (Tag 05C3), specialized to the
module given by the ring itself (blueprint: lem-sc-affine-weakass-nonzerodivisors).
For the first inclusion, if `f * y = 0` with `y ≠ 0`, then `Ann(y)` is proper
and contains `f`. There is a prime minimal over `Ann(y)`: use existence of a
prime over a proper ideal (Tag 00E0), then Zorn's lemma on primes ordered by
reverse inclusion, since intersections of chains are prime. This prime belongs
to `WeakAss A` and contains `f`.

For the reverse inclusion, let `f ∈ q` with `q` minimal over `I = Ann(y)`.
The localization of `A / I` at `q` has only one prime, so the image of `f`
is nilpotent by Tag 00EU. Clearing denominators gives `g ∉ q` and `n > 0`
with `f ^ n * g * y = 0`. Since `I ≤ q`, we have `g * y ≠ 0`. Choose the
least such `n`; then `f ^ (n - 1) * g * y` is nonzero and killed by `f`.
Thus `f` is a zero-divisor. Finally, an element is a non-zero-divisor exactly
when it kills no nonzero element, so taking complements gives the second equality.
-/
theorem zeroDivisors_eq_iUnion_weakAss (A : Type v) [CommRing A] :
    ({a : A | ∃ b : A, b ≠ 0 ∧ a * b = 0} =
      ⋃ p : WeakAss A, (p.1 : Set A)) ∧
      nonZeroDivisors A = (⋃ p : WeakAss A, (p.1 : Set A))ᶜ := by
  classical
  have hzero : {a : A | ∃ b : A, b ≠ 0 ∧ a * b = 0} =
      ⋃ p : WeakAss A, (p.1 : Set A) := by
    ext a
    constructor
    · rintro ⟨b, hb, hab⟩
      let I : Ideal A := (⊥ : Submodule A A).colon {b}
      have hI : I ≠ ⊤ := by
        intro h
        have hmem : (1 : A) ∈ I := h.symm ▸ (show (1 : A) ∈ (⊤ : Ideal A) from trivial)
        exact hb (by simpa [I, Submodule.mem_colon_singleton] using hmem)
      obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hI
      refine Set.mem_iUnion.mpr ⟨⟨p, b, hp⟩, hp.le ?_⟩
      simpa [I, Submodule.mem_colon_singleton] using hab
    · intro ha
      obtain ⟨⟨p, b, hp⟩, hap⟩ := Set.mem_iUnion.mp ha
      obtain ⟨c, hc, hac⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hp hap
      refine ⟨c * b, ?_, ?_⟩
      · simpa [Submodule.mem_colon_singleton] using hc
      · simpa [Submodule.mem_colon_singleton, mul_assoc] using hac
  refine ⟨hzero, ?_⟩
  rw [← hzero]
  ext a
  change (a ∈ nonZeroDivisors A) ↔ ¬ ∃ b : A, b ≠ 0 ∧ a * b = 0
  rw [mem_nonZeroDivisors_iff_left]
  simp only [not_exists, not_and]
  constructor
  · intro ha b hb hab
    exact hb (ha b hab)
  · intro ha b hab
    by_contra hb
    exact ha b hb hab

end Ideal
