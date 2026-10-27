/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q156
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Basic
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Choose.Sum
import Sheaf.RingTheory.DVRValuationRingCharacterization

/-!
# Kummer pole calculus

Source: Stacks Project, More on Algebra, Tags 09F2 (`lemma-prepare`) and 09F5
(`lemma-lowering-the-level`), equations `first-congruence` and `second-congruence`.
(blueprint: lem-sfb-epp-kummer-pole-calculus)

The normalized multiplicative valuation `v` satisfies `v x = WithZero.exp (-ord x)`
for nonzero `x`, and `v 0 = 0`. Thus `v x ≤ WithZero.exp (-m)` says `ord x ≥ m`,
including the convention `ord 0 = +∞`. The rational bound `ord c ≥ -n / p` is
written `v c ^ p ≤ WithZero.exp n`, so no rounding or exclusion of zero is needed.
The parameters `w`, `v`, and `e` are bound by their defining equalities.
-/

@[expose] public section

universe u v t

open scoped WithZero

namespace IsDiscreteValuationRing

/-- Kummer coefficient congruences, polynomial addition, and normalized pole estimates.

Source: Stacks Project, More on Algebra, Tags 09F2 (`lemma-prepare`) and 09F5
(`lemma-lowering-the-level`), equations `first-congruence` and `second-congruence`.
(blueprint: lem-sfb-epp-kummer-pole-calculus)

Proof:
1. In the residue field, Frobenius gives `(ζ - 1)^p = 0`, so `w` is in the maximal
   ideal. Exact order `p` gives `w ≠ 0`. The valuation arithmetic, ring characterization,
   and nonnegative-valuation-in-ring lemmas identify the maximal ideal with positive
   additive valuation, hence `e > 0`.
2. Put `b_i = choose p i / p` for `0 < i < p`. The commutative-ring binomial expansion
   of `(1 - w)^p = 1`, after cancelling `-w`, gives
   `p U = (-1)^p w^(p-1)`, with `U = 1 + ∑_{2 ≤ i < p} b_i (-w)^(i-1)` a unit.
   Therefore `p / w^(p-1)` is a unit and `ord p = (p-1)e`.
3. Binomial expansion of the displayed fraction gives leading coefficient one and
   coefficient `b_i (p / w^(p-1)) w^(i-1)` in degree `0 < i < p`. For `i ≥ 2` this
   is divisible by `w`; in degree one its difference from `-1` is divisible by `w`.
   For odd `p` this follows from `U ≡ 1`; for `p = 2` use also `2 ∈ wR`.
4. The identity `1 + w(X + Y + wXY) = (1 + wX)(1 + wY)` gives the polynomial
   addition identity after expanding and cancelling the nonzero scalar `w^p`.
5. If `ord c ≥ -n/p`, each error term `a_i c^i` has order at least `e - in/p ≥ e-n`.
   The ultrametric inequality gives both polynomial bounds, and
   `ord (wc) ≥ e - n/p > 0`. For `c = 0`, all bounds use order infinity.
6. Multiplicativity gives `ord (w^p x y) = pe + ord x + ord y ≥ pe - 2n`;
   a zero factor again gives order infinity.
7. The translated element is `c + (1 + wc)z`. It belongs to `F(z)`, and its inverse
   affine formula `z = (z_c - c)/(1 + wc)` gives the reverse generated-field inclusion.
-/
theorem kummer_pole_calculus (R : Type u) (F : Type v)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] [CharZero F]
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField R) p]
    (ζ : R) (hζ : IsPrimitiveRoot ζ p)
    (w : R) (hw : w = 1 - ζ)
    (v : Valuation F ℤᵐ⁰) (hv : v = (maximalIdeal R).valuation F)
    (e : ℤ) (he : e = -WithZero.log (v (algebraMap R F w))) :
    0 < e ∧
    (∃ P : Polynomial R,
      P.map (algebraMap R F) =
        Polynomial.C ((algebraMap R F w ^ p)⁻¹) *
          ((1 + Polynomial.C (algebraMap R F w) * Polynomial.X) ^ p - 1) ∧
      P.Monic ∧
      (∃ a : ℕ → R,
        (∀ i : ℕ, 1 ≤ i → i < p → a i ∈ Ideal.span ({w} : Set R)) ∧
        P = Polynomial.X ^ p - Polynomial.X +
          ∑ i ∈ Finset.Ico 1 p, Polynomial.C (a i) * Polynomial.X ^ i) ∧
      P.eval₂ (MvPolynomial.C : R →+* MvPolynomial (Fin 2) R)
          (MvPolynomial.X 0 + MvPolynomial.X 1 +
            MvPolynomial.C w * MvPolynomial.X 0 * MvPolynomial.X 1) =
        P.eval₂ MvPolynomial.C (MvPolynomial.X 0) +
          P.eval₂ MvPolynomial.C (MvPolynomial.X 1) +
          MvPolynomial.C (w ^ p) * P.eval₂ MvPolynomial.C (MvPolynomial.X 0) *
            P.eval₂ MvPolynomial.C (MvPolynomial.X 1) ∧
      (∀ n : ℤ, 0 ≤ n → n < (p : ℤ) * e →
        (∀ c : F, v c ^ p ≤ WithZero.exp n →
          v (P.eval₂ (algebraMap R F) c) ≤ WithZero.exp n ∧
          v (P.eval₂ (algebraMap R F) c - (c ^ p - c)) ≤ WithZero.exp (n - e) ∧
          v (algebraMap R F w * c) < 1) ∧
        (∀ x y : F, v x ≤ WithZero.exp n → v y ≤ WithZero.exp n →
          v (algebraMap R F w ^ p * x * y) ≤ WithZero.exp (2 * n - (p : ℤ) * e)))) ∧
    v (p : F) = WithZero.exp (-((p : ℤ) - 1) * e) ∧
    (∀ (E : Type t) [Field E] [Algebra F E] (z : E) (c : F),
      1 + algebraMap R F w * c ≠ 0 →
      IntermediateField.adjoin F
          ({z + algebraMap F E c + algebraMap F E (algebraMap R F w) * z *
            algebraMap F E c} : Set E) =
        IntermediateField.adjoin F ({z} : Set E)) := by
  sorry

end IsDiscreteValuationRing
