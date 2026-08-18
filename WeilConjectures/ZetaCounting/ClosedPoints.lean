/-
Copyright (c) 2026 mathhzstx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathhzstx
-/
module

public import WeilConjectures.ZetaCounting.EulerProducts

@[expose] public section

open PowerSeries

/-!
# Abstract finite-extension and closed-point interfaces

Chapter 3, §6 of `weil_conjectures_chapter3.tex` (`sec:weil-closed-point-interface`).

Two combinatorial interfaces over a finite-orbit Frobenius datum `D`: a family of finite
types of `n`-th extension points comparing with the `n`-th Frobenius fixed points, and a
type of closed points with degrees comparing with the Frobenius orbits.  No construction
of either interface from a scheme is asserted here.

## Main definitions

* `Weil.FiniteExtensionPointInterface` and its point count `pointCount`.
* `Weil.ClosedPointOrbitInterface`, its one-degree finsets `degreeClosedPointFinset` and
  counts `closedPointCount`, and its Euler product `eulerProduct`.

## Main results

* `Weil.FiniteExtensionPointInterface.countingZetaSeries_pointCount` — the zeta series of
  the extension-point counts is the zeta series of the fixed-point counts.
* `Weil.ClosedPointOrbitInterface.closedPointCount_eq_orbitCount` — closed points of one
  degree are counted by the orbits of that degree.
* `Weil.ClosedPointOrbitInterface.eulerProduct_eq_orbitEulerProduct` and
  `Weil.ClosedPointOrbitInterface.countingZetaSeries_eq_eulerProduct` — the closed-point
  Euler product is the orbit Euler product, hence the counting zeta series.
* `Weil.ClosedPointOrbitInterface.closedPointCount_eq_one_div_mul_sum_moebius_mul_pointCount`
  — Möbius recovery of the closed-point counts from the extension-point counts.
-/

namespace Weil

noncomputable section

universe u v

/-! ### The finite-extension point interface -/

/-- A finite-extension point interface over a finite-orbit datum `D`: a family of finite types
of `n`-th extension points together with, for every positive `n`, a comparison equivalence with
the fixed-point finset `Fix_D(n)`. The type and its finiteness do not depend on a positivity
proof; only the comparison equivalence takes one.
(blueprint: `def:weil-finite-extension-point-interface`) -/
structure FiniteExtensionPointInterface (D : FiniteOrbitFrobeniusData.{u}) where
  /-- The type of `n`-th extension points. -/
  points : ℕ → Type v
  /-- Each type of extension points is finite. -/
  fintype : ∀ n, Fintype (points n)
  /-- For positive `n` the `n`-th extension points are the `n`-th Frobenius fixed
  points. -/
  pointEquiv : ∀ n : ℕ, 0 < n → points n ≃ {x : D.points // x ∈ D.fixedPointFinset n}

attribute [instance] FiniteExtensionPointInterface.fintype

namespace FiniteExtensionPointInterface

variable {D : FiniteOrbitFrobeniusData} (P : FiniteExtensionPointInterface D)

/-- The finite-extension point count `N_n(P) = #(Rat_P n)`.
(blueprint: `def:weil-finite-extension-point-count`) -/
def pointCount (n : ℕ) : ℕ :=
  Fintype.card (P.points n)

/-- The finite-extension point count equals the fixed-point count: `N_n(P) = N_n(D)` for `n ≥
1`. (blueprint: `lemma:weil-finite-extension-point-count-eq-fixed`) -/
theorem pointCount_eq_fixedPointCount {n : ℕ} (hn : 1 ≤ n) :
    P.pointCount n = D.fixedPointCount n := by
  rw [pointCount, FiniteOrbitFrobeniusData.fixedPointCount, ← Fintype.card_coe]
  exact Fintype.card_congr (P.pointEquiv n hn)

/-- The finite-extension and orbit counting zeta series agree: `Z_P = Z_{cnt,D}`.
(blueprint: `prop:weil-finite-extension-zeta-eq-orbit-zeta`) -/
theorem countingZetaSeries_pointCount :
    countingZetaSeries P.pointCount = countingZetaSeries D.fixedPointCount :=
  countingZetaSeries_congr fun _ hn ↦ P.pointCount_eq_fixedPointCount hn

end FiniteExtensionPointInterface

/-! ### The closed-point–orbit interface -/

/-- A closed-point–orbit interface over `D`: a type of closed points with a degree function, an
equivalence `θ_C` with the type of Frobenius orbits, and the degree compatibility `deg_C(c) =
deg_F(θ_C(c))`. (blueprint: `def:weil-closed-point-orbit-interface`) -/
structure ClosedPointOrbitInterface (D : FiniteOrbitFrobeniusData.{u}) where
  /-- The type of closed points. -/
  ClosedPoint : Type v
  /-- The degree of a closed point. -/
  degree : ClosedPoint → ℕ
  /-- The comparison equivalence with the Frobenius orbits. -/
  orbitEquiv : ClosedPoint ≃ D.Orbit
  /-- The comparison equivalence preserves degrees. -/
  degree_eq : ∀ c, degree c = FiniteOrbitFrobeniusData.Orbit.degree (orbitEquiv c)

namespace ClosedPointOrbitInterface

open FiniteOrbitFrobeniusData

variable {D : FiniteOrbitFrobeniusData} (C : ClosedPointOrbitInterface D)

/-- Closed points have positive degree. (blueprint: `lemma:weil-closed-point-degree-positive`) -/
theorem one_le_degree (c : C.ClosedPoint) : 1 ≤ C.degree c := by
  rw [C.degree_eq]
  exact (C.orbitEquiv c).degree_pos

/-- The degree function of a closed-point interface is the orbit degree transported along the
comparison equivalence. (blueprint: `lemma:weil-closed-point-degree-comp`) -/
theorem degree_comp_orbitEquiv : C.degree = Orbit.degree ∘ C.orbitEquiv :=
  funext C.degree_eq

/-- Only finitely many closed points have bounded degree.
(blueprint: `lemma:weil-closed-point-degree-bounded-finite`) -/
theorem finite_setOf_degree_le (N : ℕ) : {c : C.ClosedPoint | C.degree c ≤ N}.Finite := by
  refine ((D.finite_setOf_degree_le N).preimage C.orbitEquiv.injective.injOn).subset
    fun c hc ↦ ?_
  rw [Set.mem_preimage, Set.mem_setOf_eq, ← C.degree_eq]
  exact hc

/-- The finset `𝒞_m` of closed points of one degree `m`.
(blueprint: `def:weil-degree-closed-point-finset`) -/
def degreeClosedPointFinset (m : ℕ) : Finset C.ClosedPoint :=
  (D.degreeOrbitFinset m).preimage C.orbitEquiv C.orbitEquiv.injective.injOn

/-- Membership in the one-degree closed-point finset.
(blueprint: `lemma:weil-degree-closed-point-finset-mem`) -/
@[simp]
theorem mem_degreeClosedPointFinset {m : ℕ} (c : C.ClosedPoint) :
    c ∈ C.degreeClosedPointFinset m ↔ C.degree c = m := by
  rw [degreeClosedPointFinset, Finset.mem_preimage, D.mem_degreeOrbitFinset, ← C.degree_eq]

/-- The number `b_m(C) = #𝒞_m` of closed points of one degree.
(blueprint: `def:weil-closed-point-count`) -/
def closedPointCount (m : ℕ) : ℕ :=
  (C.degreeClosedPointFinset m).card

/-- Closed-point degree counts equal orbit degree counts: `b_m(C) = a_m(D)`.
(blueprint: `lemma:weil-closed-point-count-eq-orbit-count`) -/
theorem closedPointCount_eq_orbitCount (m : ℕ) : C.closedPointCount m = D.orbitCount m :=
  Finset.card_equiv C.orbitEquiv fun _ ↦ Finset.mem_preimage

/-! ### The closed-point Euler product -/

/-- The closed-point Euler product `Z_{cl,C} = ∏^lf_c E_{deg_C(c)}`.
(blueprint: `def:weil-closed-point-euler-product`) -/
def eulerProduct (R : Type*) [CommRing R] : R⟦X⟧ :=
  Weil.eulerProduct R C.degree C.finite_setOf_degree_le

/-- Reindexing the closed-point product by Frobenius orbits: `Z_{cl,C} = Z_{orb,D}` over every
commutative coefficient ring. (blueprint: `prop:weil-closed-point-euler-product-reindex`) -/
theorem eulerProduct_eq_orbitEulerProduct (R : Type*) [CommRing R] :
    C.eulerProduct R = D.orbitEulerProduct R := by
  have hfin : ∀ N : ℕ,
      {c : C.ClosedPoint | (Orbit.degree ∘ C.orbitEquiv) c ≤ N}.Finite := fun N ↦
    (C.finite_setOf_degree_le N).subset fun c hc ↦ (C.degree_eq c).trans_le hc
  calc C.eulerProduct R
      = Weil.eulerProduct R (Orbit.degree ∘ C.orbitEquiv) hfin :=
        eulerProduct_congr R C.degree C.degree_comp_orbitEquiv _ _
    _ = D.orbitEulerProduct R :=
        eulerProduct_comp_equiv R Orbit.degree C.orbitEquiv _ _

/-- The closed-point Euler product has constant coefficient one.
(blueprint: `lemma:weil-closed-point-euler-product-constant`) -/
@[simp]
theorem constantCoeff_eulerProduct (R : Type*) [CommRing R] :
    constantCoeff (C.eulerProduct R) = 1 :=
  _root_.Weil.constantCoeff_eulerProduct R _ _

/-- Given both interfaces over the same datum, the counting zeta series of the extension-point
counts is the closed-point Euler product: `Z_P = Z_{cl,C}`.
(blueprint: `thm:weil-closed-point-euler-exponential`) -/
theorem countingZetaSeries_eq_eulerProduct (P : FiniteExtensionPointInterface D) :
    countingZetaSeries P.pointCount = C.eulerProduct ℚ := by
  rw [P.countingZetaSeries_pointCount, D.countingZetaSeries_eq_orbitEulerProduct,
    C.eulerProduct_eq_orbitEulerProduct]

/-- The integral closed-point Euler product is the integral orbit Euler product, and the
rational one is its image. (blueprint: `lemma:weil-integer-closed-point-euler-product-map`) -/
theorem map_eulerProduct :
    PowerSeries.map (algebraMap ℤ ℚ) (C.eulerProduct ℤ) = C.eulerProduct ℚ :=
  Weil.map_eulerProduct ℤ C.degree (algebraMap ℤ ℚ) C.finite_setOf_degree_le

/-- Closed points recovered from finite-extension point counts: `b_m(C) = (1/m) ∑_{r ∣ m} μ(r)
N_{m/r}(P)` in `ℚ` for `m ≥ 1`. (blueprint: `cor:weil-closed-point-mobius-recovery`) -/
theorem closedPointCount_eq_one_div_mul_sum_moebius_mul_pointCount
    (P : FiniteExtensionPointInterface D) {m : ℕ} (hm : 1 ≤ m) :
    (C.closedPointCount m : ℚ) =
      1 / (m : ℚ) *
        ∑ r ∈ m.divisors,
          (ArithmeticFunction.moebius r : ℚ) * (P.pointCount (m / r) : ℚ) := by
  rw [C.closedPointCount_eq_orbitCount,
    D.orbitCount_eq_one_div_mul_sum_moebius_mul_fixedPointCount hm]
  congr 1
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  rw [P.pointCount_eq_fixedPointCount
    (Nat.div_pos (Nat.divisor_le hr) (Nat.pos_of_mem_divisors hr))]

end ClosedPointOrbitInterface

end

end Weil
