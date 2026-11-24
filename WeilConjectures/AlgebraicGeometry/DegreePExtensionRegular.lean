/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Derivation.MapCoeffs
import WeilConjectures.RingTheory.HypersurfaceDerivationRegular

/-!
# Regularity of a degree-p polynomial extension

## References

* Stacks Project, Tag 07PG
-/

@[expose] public section

universe u

namespace Algebra

/-- Let `R` be a regular commutative ring, `f : R`, and `D` a derivation of `R`
with `D f` a unit.  For every positive natural number `n`, adjoining an
`n`-th root of `f` preserves regularity.  This is the statement of Stacks
Project, More on Algebra, Tag 07PG (first sentence). -/
theorem isRegularRing_quotient_X_pow_sub_of_isUnit_derivation
    (R : Type u) [CommRing R] [IsRegularRing R]
    (f : R) (D : Derivation ℤ R R) (hDf : IsUnit (D f))
    (n : ℕ) (hn : 1 ≤ n) :
    IsRegularRing
      (Polynomial R ⧸ Ideal.span ({Polynomial.X ^ n - Polynomial.C f} : Set (Polynomial R))) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  clear hn0
  let Dp : Derivation ℤ (Polynomial R) (Polynomial R) :=
    PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs
  have hDpX : Dp Polynomial.X = 0 := by
    dsimp [Dp]
    simp
  have hDpC (x : R) : Dp (Polynomial.C x) = Polynomial.C (D x) := by
    dsimp [Dp]
    simp
  have hDp : Dp (Polynomial.X ^ n - Polynomial.C f) = -Polynomial.C (D f) := by
    rw [map_sub, Dp.leibniz_pow, hDpX, smul_zero, hDpC]
    simp
  let I : Ideal (Polynomial R) := Ideal.span
    ({Polynomial.X ^ n - Polynomial.C f} : Set (Polynomial R))
  apply IsRegularRing.quotient_span_singleton_of_isUnit_derivation
      (Polynomial R) (Polynomial.X ^ n - Polynomial.C f) Dp
  rw [hDp]
  apply IsUnit.map (Ideal.Quotient.mk I)
  simpa only [map_neg] using
    IsUnit.map (Polynomial.C : R →+* Polynomial R) hDf.neg


end Algebra
