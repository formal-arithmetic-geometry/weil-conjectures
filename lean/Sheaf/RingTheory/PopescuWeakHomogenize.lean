/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Homogenizing equations evaluated in a prime localization

Source: Stacks Project, Smoothing Ring Maps, proof of Tag 07F9,
`lemma-delocalize-weak`, the homogenization and target-denominator paragraphs.
(blueprint: lem-weil-pbc-popescu-weak-homogenize)
-/

@[expose] public section

universe u v

namespace Algebra

open MvPolynomial
open scoped BigOperators

/-- Homogenize only the last `m` variables and clear their values' denominators.
The first `n` values already belong to the unlocalized ring. No smoothness,
presentation of the source, or Popescu resolution is required here.
Source: Stacks Project, proof of Tag 07F9 (`lemma-delocalize-weak`), lines 2189–2211.
(blueprint: lem-weil-pbc-popescu-weak-homogenize)

Proof: Write each of the last `m` values as a fraction and multiply their denominators
into one `w` outside `q`. Multiply each numerator by the other denominators. Choose
`dⱼ` to be the maximum extra-variable degree among the monomials of `fⱼ`, with maximum
of the empty support zero. Define `Fⱼ` by the displayed monomial formula, shifting
all old variables by one and multiplying by `X_last^(dⱼ-extra_degree)`. Assign the
first `n` coordinates their given values, the next `m` coordinates the adjusted
numerators, and the last coordinate `w`. In the localization, evaluating `Fⱼ`
equals `w^dⱼ` times the evaluation of `fⱼ`, hence is zero. For each `j`, the
localization equality criterion supplies an annihilator outside `q` for this
unlocalized evaluation. Let coordinate zero be their product. It remains outside
`q` and annihilates every evaluated `Fⱼ`. Thus evaluation kills `X₀*Fⱼ`.
When `m=0` or `c=0`, use `1` for the corresponding empty denominator product;
zero polynomials use degree zero. -/
theorem exists_homogenized_local_equations
    {R : Type u} {Λ : Type v} [CommRing R] [CommRing Λ] [Algebra R Λ]
    (q : PrimeSpectrum Λ) (n m c : ℕ)
    (f : Fin c → MvPolynomial (Fin (n + m)) R)
    (a : Fin n → Λ) (y : Fin (n + m) → Localization.AtPrime q.asIdeal)
    (hy : ∀ i : Fin n, y (Fin.castAdd m i) =
      algebraMap Λ (Localization.AtPrime q.asIdeal) (a i))
    (hf : ∀ j, aeval y (f j) = 0) :
    ∃ (d : Fin c → ℕ) (F : Fin c → MvPolynomial (Fin (n + m + 2)) R)
      (l : Fin (n + m + 2) → Λ),
      (∀ j : Fin c, ∀ e ∈ (f j).support,
        (∑ i : Fin (n + m), if n ≤ i.val then e i else 0) ≤ d j) ∧
      (∀ j : Fin c, F j =
        ∑ e ∈ (f j).support,
          MvPolynomial.C ((f j).coeff e) *
            (∏ i : Fin (n + m), X i.castSucc.succ ^ e i) *
            X (Fin.last (n + m + 1)) ^
              (d j - ∑ i : Fin (n + m), if n ≤ i.val then e i else 0)) ∧
      (∀ i : Fin n, l (Fin.castLE (Nat.le_add_right n m) i).castSucc.succ = a i) ∧
      l 0 ∉ q.asIdeal ∧ l (Fin.last (n + m + 1)) ∉ q.asIdeal ∧
      (∀ j : Fin c, aeval l (X (0 : Fin (n + m + 2)) * F j) = 0) := by sorry

end Algebra
