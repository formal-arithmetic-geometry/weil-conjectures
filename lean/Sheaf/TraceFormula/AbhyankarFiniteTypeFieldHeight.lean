/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.FieldTheory.PrimeField
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Abhyankar height bound for valuations of finitely generated fields

Source: Temkin, *Stable modification*, §2.1, Corollary 2.1.3(i), specialized to
fields finitely generated over their prime subfield (blueprint:
`lem-trf-abhyankar-finite-type-field-height`).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v

/-- A valuation ring of a field finitely generated over its prime field has height at most
transcendence degree plus one.

Source: Temkin, *Stable modification*, §2.1, Lemma 2.1.2 and Corollary 2.1.3(i), p. 8.
(blueprint: lem-trf-abhyankar-finite-type-field-height)

Proof plan:
1. Finite field generation gives a finite transcendence basis of size `d`. For a valuation
   ring `A` of `K`, restrict the valuation to the prime subfield `F`, obtaining `A_F`.
   Write `Gamma_K`, `Gamma_F` for the value groups and `kappa_K`, `kappa_F` for the
   residue fields.
2. Apply the relative Abhyankar inequality (`lem-trf-abhyankar-inequality`) to `F` in `K`:
   the rational rank of `Gamma_K / Gamma_F` plus the residue transcendence degree is
   at most `d`. Thus the quotient rational rank is at most `d`.
3. The value-group map is injective because the units of `A_F` are precisely the units
   of `A` lying in `F`. Tensor its short exact sequence with the flat integer module
   of rationals to add rational ranks. The prime-field bound
   (`lem-trf-prime-field-valuation-rank`) gives rational rank of `Gamma_F` at most one,
   hence rational rank of `Gamma_K` at most `d + 1`.
4. For any prime chain with `n` strict inclusions, `lem-trf-valuation-height-rank` bounds
   `n` by the rational rank of `Gamma_K`. Combining the bounds proves the conclusion.
-/
theorem abhyankar_finite_type_field_height
    (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]
    (hprime : (⊥ : Subfield K) = (algebraMap F K).fieldRange)
    (hfg : (⊤ : IntermediateField F K).FG)
    (d : ℕ) (hd : Algebra.trdeg F K = d) :
    ∀ (A : ValuationSubring K) (n : ℕ)
      (p : Fin (n + 1) → PrimeSpectrum A), StrictMono p → n ≤ d + 1 := by
  sorry

end
