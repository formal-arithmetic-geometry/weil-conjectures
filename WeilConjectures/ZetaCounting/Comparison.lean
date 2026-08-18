/-
Copyright (c) 2026 mathhzstx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathhzstx
-/
module

public import WeilConjectures.EulerProductAux
public import WeilConjectures.ZetaSeries
public import WeilConjectures.ZetaCounting.EulerProducts

@[expose] public section

/-!
# Comparison with the zeta series and the Euler product of `WeilConjectures`

The counting zeta series and the Euler products of
`WeilConjectures.ZetaCounting.EulerProducts` are the combinatorial counterparts of the
objects already used for schemes over a finite field.  This file identifies them:

* `Weil.countingZetaSeries_pointCount` — the counting zeta series of the point counts of
  a scheme over a finite field is `AlgebraicGeometry.Scheme.Hom.zetaSeries`;
* `Weil.eulerProduct_eq_tprod` — the locally finite Euler product of a degree function is
  Mathlib's coefficientwise infinite product `∏' i, (1 - X ^ d i)⁻¹`, which is the form
  used by `AlgebraicGeometry.Scheme.Hom.zetaSeries_eq_tprod`.

Together these say that the development of Chapter 3 and the scheme-theoretic Euler
product of `WeilConjectures.EulerProduct` describe the same power series.
-/

open PowerSeries

namespace Weil

noncomputable section

/-- An inverse Euler factor is the geometric series `(1 - T^m)⁻¹`. -/
theorem inverseEulerFactor_eq_inv_one_sub_X_pow {m : ℕ} (hm : 1 ≤ m) :
    inverseEulerFactor ℚ m = ((1 - PowerSeries.X ^ m)⁻¹ : ℚ⟦X⟧) := by
  rw [PowerSeries.inv_one_sub_X_pow_eq_mk (by omega : m ≠ 0)]
  ext n
  rw [coeff_inverseEulerFactor hm, coeff_mk]

open scoped PowerSeries.WithPiTopology in
/-- The locally finite Euler product of a degree function is the coefficientwise infinite
product `∏' i, (1 - T^{d i})⁻¹` of `PowerSeries.WithPiTopology`. -/
theorem eulerProduct_eq_tprod {ι : Type*} (d : ι → ℕ) (hd : ∀ i, 1 ≤ d i)
    (hfin : ∀ N : ℕ, {i : ι | d i ≤ N}.Finite) :
    eulerProduct ℚ d hfin = ∏' i, ((1 - PowerSeries.X ^ d i)⁻¹ : ℚ⟦X⟧) := by
  ext n
  have hT : ∀ i, d i ≤ n → i ∈ (hfin n).toFinset := fun i hi ↦
    (hfin n).mem_toFinset.mpr hi
  rw [agreeThrough_eulerProduct_prod ℚ d hfin hT n le_rfl,
    PowerSeries.coeff_tprod_inv_one_sub_X_pow (fun i ↦ by have := hd i; omega) hfin n hT]
  exact congrArg _
    (Finset.prod_congr rfl fun i _ ↦ inverseEulerFactor_eq_inv_one_sub_X_pow (hd i))

/-- The counting zeta series of the point counts of a scheme over a finite field is its
zeta series `Z(X, t) = Exp(∑ N_n tⁿ/n)`. -/
theorem countingZetaSeries_pointCount {S : AlgebraicGeometry.Scheme.{u}} {k : Type u}
    [Field k] (f : S.Hom (AlgebraicGeometry.Spec (.of k))) :
    countingZetaSeries f.pointCount = f.zetaSeries :=
  rfl

end

end Weil
