/-
Copyright (c) 2026 mathhzstx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathhzstx
-/
module

public import WeilConjectures.EulerProduct

@[expose] public section

/-!
# The zeta series of a scheme over a finite field, grouped by degree, and its integrality

For a scheme `X` of finite type over a finite field `k`, given by a structure morphism
`f : X ⟶ Spec k`, the Euler product `Z(X, t) = ∏ (1 - t ^ deg x)⁻¹` over the closed
points of `X` is `AlgebraicGeometry.Scheme.Hom.zetaSeries_eq_tprod`. This file records
its two immediate consequences: grouping the closed points by degree gives the classical
form `Z(X, t) = ∏_m (1 - t ^ m) ^ (-a_m)` with `a_m` the number of closed points of
degree `m`, and reading off the coefficients of a finite subproduct shows that
`Z(X, t) ∈ ℤ⟦t⟧`.

## Main results

- `AlgebraicGeometry.Scheme.Hom.zetaSeries_eq_tprod_pow`
- `AlgebraicGeometry.Scheme.Hom.coeff_zetaSeries_mem_range` and
  `AlgebraicGeometry.Scheme.Hom.exists_map_intCast_eq_zetaSeries`, the coefficientwise
  and the typed form of the integrality of the zeta series
-/

universe u

open CategoryTheory PowerSeries

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k] [Finite k] (f : X ⟶ Spec (.of k))

/-- The number of closed points of `X` of degree `m` over the base field.
(blueprint: `def:weil-closed-point-count`) -/
noncomputable def Hom.closedPointCount (m : ℕ) : ℕ :=
  {x : X.finitePoints | f.degreeOver x.1 = m}.ncard

/-- There is no closed point of degree zero.
(blueprint: `lemma:weil-closed-point-count-zero`) -/
@[simp]
theorem Hom.closedPointCount_zero : f.closedPointCount 0 = 0 := by
  have hempty : {x : X.finitePoints | f.degreeOver x.1 = 0} = ∅ :=
    Set.eq_empty_of_forall_notMem fun x hx ↦ f.degreeOver_ne_zero x.2 hx
  rw [Hom.closedPointCount, hempty, Set.ncard_empty]

variable [QuasiCompact f] [LocallyOfFiniteType f]

/-- The point counts of `X` are the degree-weighted closed point counts:
`N_n = ∑_{m ∣ n} m * a_m`. (blueprint: `prop:weil-point-count-eq-sum-closed-point-count`) -/
theorem Hom.pointCount_eq_sum_divisors_mul_closedPointCount {n : ℕ} (hn : n ≠ 0) :
    f.pointCount n = ∑ m ∈ n.divisors, m * f.closedPointCount m := by
  classical
  rw [f.pointCount_eq_sum hn
    (T := (f.finite_setOf_degreeOver_le n).toFinset) fun x hx ↦
      (f.finite_setOf_degreeOver_le n).mem_toFinset.mpr
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hx)]
  exact sum_filter_dvd_eq_sum_divisors_mul_ncard hn fun x hx ↦
    (f.finite_setOf_degreeOver_le n).mem_toFinset.mpr
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hx)

open scoped PowerSeries.WithPiTopology in
/-- **The degree-grouped Euler product** of the zeta function of a scheme of finite type
over a finite field: `Z(X, t) = ∏_m (1 - t ^ m) ^ (-a_m)`, where `a_m` is the number of
closed points of degree `m`. (blueprint: `cor:weil-zeta-degree-euler-product`) -/
theorem Hom.zetaSeries_eq_tprod_pow :
    f.zetaSeries =
      ∏' m : ℕ, ((1 - PowerSeries.X ^ m : PowerSeries ℚ)⁻¹) ^ f.closedPointCount m := by
  rw [f.zetaSeries_eq_countingZetaSeries]
  exact countingZetaSeries_eq_tprod_pow f.closedPointCount_zero fun n hn ↦
    f.pointCount_eq_sum_divisors_mul_closedPointCount hn

/-- **The coefficients of the zeta function are integers.**
(blueprint: `cor:weil-zeta-coefficients-integral`) -/
theorem Hom.coeff_zetaSeries_mem_range (n : ℕ) :
    coeff n f.zetaSeries ∈ (Int.castRingHom ℚ).range := by
  rw [f.zetaSeries_eq_countingZetaSeries]
  exact coeff_countingZetaSeries_mem_range (fun x ↦ f.degreeOver_ne_zero x.2)
    f.finite_setOf_degreeOver_le (fun _ hn _ hT ↦ f.pointCount_eq_sum hn hT) n

/-- **The zeta function lifts to `ℤ⟦t⟧`.**
(blueprint: `cor:weil-zeta-integral-lift`) -/
theorem Hom.exists_map_intCast_eq_zetaSeries :
    ∃ Z : PowerSeries ℤ, map (Int.castRingHom ℚ) Z = f.zetaSeries :=
  exists_map_eq_of_forall_coeff_mem_range _ f.coeff_zetaSeries_mem_range

end AlgebraicGeometry.Scheme

end
