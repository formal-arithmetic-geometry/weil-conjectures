/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.RingTheory.Algebraic.Defs

/-! # A simultaneous transcendental element at finitely many primes

Source: Stacks Project, More on Morphisms, Tag 0GTE, `lemma-silly`
(blueprint: lem-trf-finite-prime-transcendental-coordinate).
-/

@[expose] public section

universe u

namespace Ideal

/-- An ideal avoiding finitely many incomparable primes contains an element whose images
in their residue fields are transcendental over the prescribed subfields.

Source: Stacks Project, More on Morphisms, Tag 0GTE, `lemma-silly`
(blueprint: lem-trf-finite-prime-transcendental-coordinate).

Proof plan. If `r = 0`, take `x = 0`; the indexed conclusion is empty. Otherwise, for each
`i`, form `Jᵢ = J * ∏ j ≠ i, (p j).asIdeal`. Choose an element of `J` outside `p i` and,
for each `j ≠ i`, an element of `p j` outside `p i`. Their product belongs to `Jᵢ` and is
outside `p i` by primality, so `Jᵢ` is not contained in `p i` (Stacks Tag 07K1).

Identify the residue field at `p i` with the fraction field of `B / (p i).asIdeal`:
localizing `B` at `p i` and then quotienting its maximal ideal is the same as
localizing this domain at all its nonzero elements. Nonalgebraicity provides a
transcendental fraction `ξ = u / v`. Multiply numerator and denominator by an element
of `Jᵢ` outside `p i` to obtain `ξ = a / b` with `a, b ∈ Jᵢ` and `b ∉ p i`. If both
images were algebraic over `k i`, their quotient would be algebraic as well, a
contradiction. Choose `xᵢ` to be one with transcendental image.

Finally set `x = ∑ i, xᵢ`. Each summand belongs to `J`. Modulo `p i`, all summands
except `xᵢ` vanish because their defining product contains `p i`. Thus the image
of `x` equals the transcendental image of `xᵢ` at every prime.
-/
theorem exists_mem_transcendental_residueFields
    {B : Type u} [CommRing B] (r : ℕ) (p : Fin r → PrimeSpectrum B)
    (hincomparable : ∀ i j : Fin r, i ≠ j → ¬ (p i).asIdeal ≤ (p j).asIdeal)
    (k : (i : Fin r) → Subfield (p i).asIdeal.ResidueField)
    (hnot_algebraic : ∀ i : Fin r, ¬ Algebra.IsAlgebraic (k i) (p i).asIdeal.ResidueField)
    (J : Ideal B) (hJ : ∀ i : Fin r, ¬ J ≤ (p i).asIdeal) :
    ∃ x ∈ J, ∀ i : Fin r,
      Transcendental (k i) (algebraMap B (p i).asIdeal.ResidueField x) := by
  sorry

end Ideal
