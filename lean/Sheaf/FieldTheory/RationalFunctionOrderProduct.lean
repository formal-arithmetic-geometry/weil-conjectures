/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Pole orders of products of integer powers of polynomials

Source: blueprint `sec-zeta-weil/sk-thm-weil4/thm-weil-final-betti.md`, proof, paragraphs 2–4
(blueprint: lem-weil-rational-function-order-product).

## Main statements

* `Polynomial.rootMultiplicity_orderProduct_facts`: polynomial multiplicity identities.
* `RatFunc.rootMultiplicity_prod_zpow`: signed multiplicity, pole order and regularity.
* `RatFunc.rootMultiplicity_denom_prod_zpow_eq_one`: an isolated simple denominator factor.

Pole order is expressed by the multiplicity of the reduced denominator, exactly as in the
Mathlib match of `def-weil-rational-function-pole-order`. Regularity means that this denominator
has nonzero value at the point. The numerator and denominator are Mathlib's canonical reduced
presentation, whose denominator is monic and coprime to the numerator.
-/

@[expose] public section

universe u

open Polynomial
open scoped BigOperators

namespace Polynomial

/-- Polynomial facts used to compute pole orders, clause 1 of
(blueprint: lem-weil-rational-function-order-product).
Source: blueprint `sec-zeta-weil/sk-thm-weil4/thm-weil-final-betti.md`, proof, paragraphs 2–4.

Proof (steps 1–2 of the node): `lem-weil-root-multiplicity-pos-iff`
(`Polynomial.rootMultiplicity_pos`) gives the zero-multiplicity criterion for nonzero `P`.
`lem-weil-root-multiplicity-mul` (`Polynomial.rootMultiplicity_mul`) gives additivity for
nonzero products. A nonzero constant has multiplicity zero, while `X - C c` has multiplicity
one: its square cannot divide a polynomial of degree one. Apply additivity to their product.
For `c ≠ 0`, factor `1 - C c⁻¹ * X` as `C (-c⁻¹) * (X - C c)` and apply the linear-factor
identity. -/
theorem rootMultiplicity_orderProduct_facts {K : Type u} [Field K]
    (c : K) (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (rootMultiplicity c P = 0 ↔ P.eval c ≠ 0) ∧
    rootMultiplicity c (P * Q) = rootMultiplicity c P + rootMultiplicity c Q ∧
    (∀ v : Kˣ, rootMultiplicity c (C (v : K) * (X - C c)) = 1) ∧
    (c ≠ 0 → rootMultiplicity c (1 - C c⁻¹ * X) = 1) := by
  sorry

end Polynomial

namespace RatFunc

/-- Signed multiplicity and pole order for a product, clause 2 of
(blueprint: lem-weil-rational-function-order-product).
Source: blueprint `sec-zeta-weil/sk-thm-weil4/thm-weil-final-betti.md`, proof, paragraphs 2–4.

Proof (steps 3–7 of the node): separate the positive and negative exponents into polynomial
products `A` and `B`; the zero exponents contribute one. Every factor is nonzero, hence so are
`A`, `B`, and `R = A / B`. Repeated use of `lem-weil-root-multiplicity-mul` gives that the
multiplicity of `A` minus that of `B` is the displayed signed sum. Cross-multiply the reduced
presentation `R.num / R.denom = A / B` to get `R.num * B = A * R.denom`, and apply additivity
again to obtain the same difference for the reduced numerator and denominator. If both had
positive multiplicity, `X - C c` would divide both. Coprimality supplies a Bezout combination
one, so it would divide one, contradicting its degree. Thus one multiplicity is zero.
For `m ≥ 1`, denominator multiplicity `m` is now equivalent to signed sum `-m`.
Finally `lem-weil-root-multiplicity-pos-iff` identifies denominator nonvanishing with zero
multiplicity; using the preceding disjunction, this is equivalent to a nonnegative signed sum.
The pole and regularity interpretations are those of `def-weil-rational-function-pole-order`
and `def-weil-rational-function-field`. -/
theorem rootMultiplicity_prod_zpow {K : Type u} [Field K]
    (c : K) (n : ℕ) (P : Fin (n + 1) → K[X]) (e : Fin (n + 1) → ℤ)
    (hP : ∀ j : Fin (n + 1), P j ≠ 0) (R : RatFunc K)
    (hR : R = ∏ j : Fin (n + 1), (algebraMap K[X] (RatFunc K) (P j)) ^ e j) :
    R ≠ 0 ∧
    (rootMultiplicity c R.num : ℤ) - (rootMultiplicity c R.denom : ℤ) =
      ∑ j : Fin (n + 1), e j * (rootMultiplicity c (P j) : ℤ) ∧
    (rootMultiplicity c R.num = 0 ∨ rootMultiplicity c R.denom = 0) ∧
    (∀ m : ℤ, 1 ≤ m →
      ((rootMultiplicity c R.denom : ℤ) = m ↔
        (∑ j : Fin (n + 1), e j * (rootMultiplicity c (P j) : ℤ)) = -m)) ∧
    (R.denom.eval c ≠ 0 ↔
      0 ≤ ∑ j : Fin (n + 1), e j * (rootMultiplicity c (P j) : ℤ)) := by
  sorry

/-- An isolated simple denominator factor gives a simple pole, clause 3 of
(blueprint: lem-weil-rational-function-order-product).
Source: blueprint `sec-zeta-weil/sk-thm-weil4/thm-weil-final-betti.md`, proof, paragraphs 3–4.

Proof (step 8 of the node): by `lem-weil-root-multiplicity-pos-iff`, each factor other than
`j₀` has multiplicity zero at `c`. The remaining contribution to the signed sum in
`rootMultiplicity_prod_zpow` is `(-1) * 1 = -1`. Apply its pole-order equivalence with `m = 1`.
Denominator multiplicity one is precisely the pole-order notion of
`def-weil-rational-function-pole-order`. -/
theorem rootMultiplicity_denom_prod_zpow_eq_one {K : Type u} [Field K]
    (c : K) (n : ℕ) (P : Fin (n + 1) → K[X]) (e : Fin (n + 1) → ℤ)
    (hP : ∀ j : Fin (n + 1), P j ≠ 0) (R : RatFunc K)
    (hR : R = ∏ j : Fin (n + 1), (algebraMap K[X] (RatFunc K) (P j)) ^ e j)
    (j₀ : Fin (n + 1)) (he : e j₀ = -1) (hm : rootMultiplicity c (P j₀) = 1)
    (hother : ∀ j : Fin (n + 1), j ≠ j₀ → (P j).eval c ≠ 0) :
    rootMultiplicity c R.denom = 1 := by
  sorry

end RatFunc
