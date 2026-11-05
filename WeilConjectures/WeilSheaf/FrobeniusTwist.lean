/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TateTwistCohomology
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Geometric Frobenius on the coefficient twists

Let `k₀` be a finite field with `q` elements, `k̄` an algebraic closure, `σ : k̄ ≅ k̄` the geometric
Frobenius (the inverse of `x ↦ x ^ q`) and `ℓ ≠ p` a prime. The geometric Frobenius acts on the
Tate twists by `q^{-m}` (blueprint `def-weil-frobenius-coefficient-twists`), at every coefficient
stage:

* at the finite stages, on `μ_{ℓ^N}(k̄)`: `σ(ζ) = ζ^{c}` with `c q = 1` in `ℤ/ℓ^N`
  (`AlgebraicGeometry.WeilSheaf.modularCyclotomicCharacter_geometricFrobenius_mul`);
* at the integral stage, on `ℤ_ℓ(1)`: the `ℓ`-adic cyclotomic character of `σ` is `q⁻¹`
  (`AlgebraicGeometry.WeilSheaf.cyclotomicCharacter_geometricFrobenius_mul`); its reductions are
  the finite-stage values;
* at the stage `ℚ̄_ℓ`, on the Tate Weil sheaves: `ℚ̄_ℓ(m)` is the constant Weil twist of `ℚ̄_ℓ` by
  the scalar `q^{-m}` (`AlgebraicGeometry.WeilSheaf.exists_tateTwistSheaf_iso_constantTwist`),
  and in particular `ℚ̄_ℓ(-d)` is the twist by `q^d`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf

variable (k₀ : Type u) [Field k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Fintype

variable [Fintype k₀]

omit [Fintype k₀] in
variable [Finite k₀] in
/-- `ℓ ≠ p` is nonzero in the algebraic closure of `k₀`. -/
lemma neZero_natCast_algebraicClosure : NeZero ((l : ℕ) : AlgebraicClosure k₀) := ⟨by
  rw [← map_natCast (algebraMap k₀ (AlgebraicClosure k₀)),
    map_ne_zero_iff _ (algebraMap k₀ (AlgebraicClosure k₀)).injective, Ne, ringChar.spec,
    Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime k₀ _) Fact.out]
  exact Fact.out⟩

end Fintype

variable [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

end WeilSheaf

end AlgebraicGeometry
