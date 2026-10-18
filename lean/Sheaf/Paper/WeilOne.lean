/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.JacobsonSpace
public import WeilConjectures.ZetaSeries
import WeilConjectures.PointCount
import WeilConjectures.EulerProduct
import WeilConjectures.Statement

/-!
# Rationality and the Euler product: the first Weil conjecture

Source: Weil conjectures blueprint, main-20261015, `sec-zeta-weil/sk-thm-weil1/_section.md`
(blueprint: sk-thm-weil1).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped PowerSeries.WithPiTopology

namespace AlgebraicGeometry.Scheme

/-- The zeta series of any finite-type scheme over a finite field has a normalized integral
polynomial presentation, is an integral rational series with constant coefficient one, and
is the Euler product over its closed points.

Source: blueprint main-20261015, `sec-zeta-weil/sk-thm-weil1/_section.md`
(blueprint: sk-thm-weil1).

Proof plan:
1. Apply `sk-thm-rationality` with the given locally finite type and quasi-compact structure
   morphism. It gives integral polynomials A and B, B(0) = 1, B Z = A, and membership in
   the rational series with integral coefficients and constant coefficient one. The explicit
   rational-polynomial witness below is the convention of `def-weil-rational-power-series`.
2. Identify the series of `sk-def-zeta` and `def-weil-point-counts-zeta`: their finite-field
   extensions are isomorphic over the base, so their rational point sets have equal finite
   cardinalities; the infinite-cardinality convention never applies here. Both degrees are
   the residue-field degrees. Apply `prop-euler-product` to this same finite-type scheme.
   Its coefficientwise locally finite product gives the last equality. The upstream form
   indexes points with finite residue field; these are exactly the closed points, by the
   Nullstellensatz for schemes locally of finite type over a finite field. No separatedness,
   smoothness, or properness hypothesis is used. -/
theorem Hom.zetaSeries_rational_and_eulerProduct
    {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [QuasiCompact f] [LocallyOfFiniteType f] :
    (∃ A B : Polynomial ℤ, B.coeff 0 = 1 ∧
      (B.map (Int.castRingHom ℚ) : PowerSeries ℚ) * f.zetaSeries =
        (A.map (Int.castRingHom ℚ) : PowerSeries ℚ)) ∧
    ((∃ Z : PowerSeries ℤ, PowerSeries.constantCoeff Z = 1 ∧
        PowerSeries.map (Int.castRingHom ℚ) Z = f.zetaSeries) ∧
      (∃ P Q : Polynomial ℚ, Q.coeff 0 ≠ 0 ∧
        (Q : PowerSeries ℚ) * f.zetaSeries = (P : PowerSeries ℚ))) ∧
    f.zetaSeries =
      ∏' x : closedPoints X, (1 - PowerSeries.X ^ f.degreeOver x.1 : PowerSeries ℚ)⁻¹ :=
  sorry

end AlgebraicGeometry.Scheme
