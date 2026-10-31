/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedWeilModules
public import WeilConjectures.ZetaSeries
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.PowerSeries.Basic

import WeilConjectures.RingTheory.PowerSeriesHankelRank
import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
import WeilConjectures.ZetaLinearAlgebra.DetTrace
import WeilConjectures.LinearAlgebra.MatrixRankFieldExtension
import WeilConjectures.WeilSheaf.Finiteness
import WeilConjectures.PointCount
import WeilConjectures.ZetaFunction.TraceFormula
import WeilConjectures.ZetaLinearAlgebra.RationalityCriterion

/-! # Rationality for separated finite-type schemes with condensed coefficients

Source: latest blueprint, `cor-trf-point-counting` and the rational-descent paragraph
of `sk-cor-tf-point-counting.proof.md`
(blueprint: lem-zl-separated-condensed-zeta-rationality).

The coefficient ring on `D.geometricFiber Y₀` is the pullback of the condensed
algebraic closure, with its canonical constant Weil structure. This is fixed
notation in the node, rather than an additional variable or hypothesis: the
conclusion concerns only the point-count zeta series and coefficient extension.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- The point-count zeta series of a separated finite-type scheme is rational over
an algebraic closure of the l-adic numbers, rational over the rationals, and integral
with constant coefficient one.

Source: latest blueprint, `cor-trf-point-counting`, order 3867, and the separated-case
rational-descent argument of `sk-cor-tf-point-counting.proof.md`
(blueprint: lem-zl-separated-condensed-zeta-rationality).

Proof plan:
1. Over E = Q_l use `prop-cohomological-finiteness` and the constant-coefficient
clause of `prop-every-iterate-trace`. Compact cohomology has finitely many nonzero
finite-dimensional degrees, and its alternating Frobenius traces give every positive
extension point count. The constant coefficients are the pulled-back condensed ring
with the canonical Weil structure, including for the empty scheme.
2. For each degree put C_i = det(1 - T F_i), whose constant coefficient is one.
`lem-weil-exp-trace-determinant`, `lem-weil-exp-coefficientwise-map` and
`lem-weil-power-series-exp-hom` identify the coefficient extension of Z with the
finite signed product of the C_i. Characteristic zero is supplied by
`lem-weil-integers-injective-char-zero`.
3. Multiply the even-degree factors into the denominator and the odd-degree factors
into the numerator. The denominator has constant coefficient one, including empty
products, and multiplication cancels its inverse in the power-series ring.
4. By `prop-weil-rationality-criterion` the Hankel ranks over E are uniformly bounded.
`lem-weil-matrix-rank-field-extension` gives the same bounds over Q, and the reverse
implication of the criterion gives a normalized rational polynomial fraction over Q.
5. `prop-euler-product` gives an integral power series with constant coefficient one.
Extend the rational fraction coefficientwise along Q to the chosen algebraic closure;
coefficient maps preserve multiplication and polynomial inclusion, giving P and Q
with Q(0) = 1 in the first clause. -/
theorem separated_condensed_zeta_rationality
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (Qbar : Type v) [Field Qbar] [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]
    (Y₀ : Over (Spec (CommRingCat.of D.k₀)))
    [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] :
    (∃ P Q : Polynomial Qbar, Q.coeff 0 = 1 ∧
      (Q : PowerSeries Qbar) *
          PowerSeries.map ((algebraMap (Padic l) Qbar).comp (algebraMap ℚ (Padic l)))
            Y₀.hom.zetaSeries = (P : PowerSeries Qbar)) ∧
    (∃ P Q : Polynomial ℚ, Q.coeff 0 ≠ 0 ∧
      (Q : PowerSeries ℚ) * Y₀.hom.zetaSeries = (P : PowerSeries ℚ)) ∧
    (∃ Z : PowerSeries ℤ, PowerSeries.constantCoeff Z = 1 ∧
      PowerSeries.map (Int.castRingHom ℚ) Z = Y₀.hom.zetaSeries) := by
  sorry

end WeilConjectures
