/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.BettiNumbers
public import WeilConjectures.ZetaFunction.IntegralFrobeniusFactors

/-!
# Betti numbers of a smooth proper variety

Let `X₀` be a smooth, proper, geometrically connected scheme of pure dimension `d` over
`k₀ = 𝔽_q`, with integral Frobenius factors `P₀, …, P_{2d}` and Betti numbers `bᵢ = deg Pᵢ`.
Then `bᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every `ℓ ≠ p`, `bᵢ = b_{2d-i}`, `b₀ = b_{2d} = 1`,
`P₀ = 1 - T` and `P_{2d} = 1 - qᵈ T`; consequently `Z(X₀, T)` has a pole of order exactly one at
`T = 1` and, for `d ≥ 1`, at `T = q^{-d}` (blueprint `sk-thm-betti`).

## Main statements

- `AlgebraicGeometry.Scheme.natDegree_eq_finrank_of_isIntegralFrobeniusFactor`:
  `deg Pᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` (`prop-weil-realization-independent-degrees`).
- `AlgebraicGeometry.Scheme.weilBettiNumber_eq_finrank`: `bᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for all
  `i ∈ ℤ` (`prop-weil-betti-comparison`).
- `AlgebraicGeometry.Scheme.bettiSymmetry`: blueprint `sk-thm-betti`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

namespace Scheme

variable (k₀) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `prop-weil-realization-independent-degrees`: the degree of an integral Frobenius
factor in degree `i` is `dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every prime `ℓ ≠ p`: scalar extension along the
injective `ℤ → ℚ̄_ℓ` preserves degrees, and `deg P_{i,ℓ} = dim Hⁱ`
(`AlgebraicGeometry.Scheme.natDegree_frobeniusCharpolyRev`). In particular the degree does not
depend on `ℓ`. -/
theorem natDegree_eq_finrank_of_isIntegralFrobeniusFactor
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] {i : ℤ} {P : Polynomial ℤ}
    (hP : IsIntegralFrobeniusFactor k₀ X i P) (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] :
    P.natDegree =
      Module.finrank (PadicAlgCl l) ((WeilSheaf.adicConstant k₀ l X).cohomology i).carrier := by
  rw [← natDegree_frobeniusCharpolyRev, ← hP l,
    Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]

/-- Blueprint `prop-weil-betti-comparison` (Betti-number comparison): for `X₀` smooth, proper
and geometrically connected of pure dimension `d` with integral Frobenius factors `Pᵢ`, the Betti
numbers `bᵢ` (`AlgebraicGeometry.weilBettiNumber`; `deg Pᵢ` for `0 ≤ i ≤ 2d` and `0` otherwise)
satisfy `bᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every `i ∈ ℤ` and every prime `ℓ ≠ p`; in particular they
do not depend on `ℓ`. -/
theorem weilBettiNumber_eq_finrank (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) (l : ℕ)
    [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (i : ℤ) :
    weilBettiNumber P i =
      Module.finrank (PadicAlgCl l) ((WeilSheaf.adicConstant k₀ l X).cohomology i).carrier :=
  sorry

/-- Blueprint `sk-thm-betti` (Betti symmetry and the endpoint factors): for `X₀` smooth, proper
and geometrically connected of pure dimension `d` over `k₀ = 𝔽_q`, with integral Frobenius
factors `Pᵢ` and Betti numbers `bᵢ = deg Pᵢ`:

* `bᵢ = dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` for every prime `ℓ ≠ p`;
* `bᵢ = b_{2d-i}` and `b₀ = b_{2d} = 1`;
* `P₀ = 1 - T` and `P_{2d} = 1 - qᵈ T`;
* `Z(X₀, T) = ∏_{i odd} Pᵢ / ∏_{i even} Pᵢ` has a pole of order exactly one at `T = 1`: the
  denominator vanishes there to order one and the numerator does not vanish there; and, if
  `d ≥ 1`, likewise at `T = q^{-d}`. -/
theorem bettiSymmetry (d : ℕ) [IsProper (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X ↘ Spec (CommRingCat.of k₀))] {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hP : ∀ i : Fin (2 * d + 1), IsIntegralFrobeniusFactor k₀ X (i : ℕ) (P i)) :
    (∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] (i : Fin (2 * d + 1)),
      (P i).natDegree = Module.finrank (PadicAlgCl l)
        ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier) ∧
    (∀ i : Fin (2 * d + 1), (P i.rev).natDegree = (P i).natDegree) ∧
    (P 0).natDegree = 1 ∧ (P (Fin.last (2 * d))).natDegree = 1 ∧
    P 0 = 1 - Polynomial.X ∧
    P (Fin.last (2 * d)) = 1 - C ((Nat.card k₀ : ℤ) ^ d) * Polynomial.X ∧
    ((∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1),
        (P i).map (Int.castRingHom ℚ)).rootMultiplicity 1 = 1 ∧
      ¬ (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1),
        (P i).map (Int.castRingHom ℚ)).IsRoot 1) ∧
    (1 ≤ d →
      (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Even i.1),
        (P i).map (Int.castRingHom ℚ)).rootMultiplicity ((Nat.card k₀ : ℚ) ^ d)⁻¹ = 1 ∧
      ¬ (∏ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ Odd i.1),
        (P i).map (Int.castRingHom ℚ)).IsRoot ((Nat.card k₀ : ℚ) ^ d)⁻¹) :=
  sorry

end Scheme

end AlgebraicGeometry
