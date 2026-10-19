/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Sheaf.LinearAlgebra.Matrix.MinorIdeal
public import WeilConjectures.RingTheory.Depth
import Sheaf.LinearAlgebra.Matrix.MinorIdealInclusions
import WeilConjectures.RingTheory.DepthLeSupportDimension
import WeilConjectures.RingTheory.DepthOverQuotientRing
import WeilConjectures.RingTheory.DepthQuotSMulTop
import Sheaf.RingTheory.FormalJacobianMinorInvariance
import Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete
import Sheaf.RingTheory.PowerSeriesFullCoordinatesField
import Sheaf.RingTheory.PowerSeriesQuotientVariables
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.TraceFormula.FormalBinaryMorse
import Sheaf.TraceFormula.RegularSurfaceDepthOnePrincipal

/-!
# Formal Jacobian quadratic criterion

Source: Stacks Project, Curves, Tags 0C4C and 0C49
(blueprint: lem-trf-formal-jacobian-quadratic-criterion).
-/

@[expose] public section

universe u

open Set

namespace MvPowerSeries

/-- The Jacobian matrix of a finite power-series presentation, reduced modulo its ideal.
Source: Stacks Project, Curves, Tags 0C4B and 0C4C
(blueprint: lem-trf-formal-jacobian-quadratic-criterion). -/
noncomputable def formalJacobianMatrix (F : Type u) [Field F] (n s : ℕ)
    (I : Ideal (MvPowerSeries (Fin n) F)) (f : Fin s → MvPowerSeries (Fin n) F) :
    Matrix (Fin n) (Fin s) (MvPowerSeries (Fin n) F ⧸ I) :=
  fun i j => Ideal.Quotient.mk I (MvPowerSeries.pderiv F i (f j))

/-- The ideal of `(n - 1)`-minors of the formal Jacobian matrix.
Source: Stacks Project, Curves, Tags 0C4B and 0C4C
(blueprint: lem-trf-formal-jacobian-quadratic-criterion). -/
noncomputable def formalJacobianIdeal (F : Type u) [Field F] (n s : ℕ)
    (I : Ideal (MvPowerSeries (Fin n) F)) (f : Fin s → MvPowerSeries (Fin n) F) :
    Ideal (MvPowerSeries (Fin n) F ⧸ I) :=
  Matrix.minorIdeal n s (n - 1) (formalJacobianMatrix F n s I f)

/-- The image of the maximal ideal in a power-series quotient.
Source: Stacks Project, Curves, Tags 0C4C and 0C49
(blueprint: lem-trf-formal-jacobian-quadratic-criterion). -/
noncomputable def formalJacobianMaximalIdeal (F : Type u) [Field F] (n : ℕ)
    (I : Ideal (MvPowerSeries (Fin n) F)) :
    Ideal (MvPowerSeries (Fin n) F ⧸ I) :=
  Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) F))

/-- A depth-one formal Jacobian presentation is exactly a nondegenerate binary quadratic
hypersurface, including the ring-isomorphism form. Source: Stacks Project, Curves, Tags 0C4C
and 0C49 (blueprint: lem-trf-formal-jacobian-quadratic-criterion).

Proof plan. First use the Cohen power-series regularity theorem, Nakayama, full power-series
coordinates, and quotient-by-variables to reduce to a minimal presentation `S/H` with
`H ⊆ (z₁, …, zₑ)^2`. The Jacobian-minor invariance statement and the minor-inclusion
statement identify the original ideal with the ideal of `(e - 1)`-minors of the residual
Jacobian, including the cases `e = 0, 1`; hence it is contained in the `(e - 1)`-st
power of the maximal ideal. Under the depth and maximal-Jacobian hypotheses, Nakayama
rules out `e ≥ 3` and the field case rules out `e ≤ 1`, so `e = 2`. The regular-surface
principal-kernel statement gives `H = (f)` with nonzero `f` and no terms of degree below
two. The two residual derivatives have linear parts `2a u + b v` and `b u + 2c v`,
so the maximal-Jacobian equality is equivalent to `4ac - b^2 ≠ 0`. Formal binary Morse
normalization then gives the complete local `F`-algebra isomorphism to the quadratic
model, proving (a) implies (b), and forgetting structure gives (c). Conversely, the
quadratic model has depth one by regularity of the two parameters, the depth bound, depth
drop by its nonzero nonzerodivisor equation, and depth-over-quotient comparison. A ring
isomorphism transfers the residue-field map, cotangent space, and the one-dimensional
kernel of multiplication `Sym^2(m/m^2) → m^2/m^3`; semilinear change of basis multiplies
the polar determinant by a square and a residue-field automorphism. Thus the minimal
presentation has a nondegenerate quadratic part, whose derivatives generate the maximal
ideal by Nakayama, and Jacobian-minor invariance returns the original ideal. This proves
(c) implies (a) without assuming that the ring isomorphism is `F`-linear. -/
theorem formal_jacobian_quadratic_criterion
    (F : Type u) [Field F] (n s : ℕ) (hn : 2 ≤ n)
    (I : Ideal (MvPowerSeries (Fin n) F))
    (hI : I ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin n) F))
    (f : Fin s → MvPowerSeries (Fin n) F)
    (hgen : I = Ideal.span (Set.range f)) :
    ((Ideal.depth (formalJacobianMaximalIdeal F n I)
        (MvPowerSeries (Fin n) F ⧸ I) = (1 : ℕ∞) ∧
      formalJacobianIdeal F n s I f = formalJacobianMaximalIdeal F n I) ↔
      ∃ (a b c : F), b ^ 2 - 4 * a * c ≠ 0 ∧
        Nonempty
          ((MvPowerSeries (Fin n) F ⧸ I) ≃ₐ[F]
            (MvPowerSeries (Fin 2) F ⧸
              Ideal.span ({MvPowerSeries.C a * (MvPowerSeries.X 0) ^ 2 +
                MvPowerSeries.C b * (MvPowerSeries.X 0 * MvPowerSeries.X 1) +
                MvPowerSeries.C c * (MvPowerSeries.X 1) ^ 2} :
                Set (MvPowerSeries (Fin 2) F))))) ∧
    ((∃ (a b c : F), b ^ 2 - 4 * a * c ≠ 0 ∧
        Nonempty
          ((MvPowerSeries (Fin n) F ⧸ I) ≃ₐ[F]
            (MvPowerSeries (Fin 2) F ⧸
              Ideal.span ({MvPowerSeries.C a * (MvPowerSeries.X 0) ^ 2 +
                MvPowerSeries.C b * (MvPowerSeries.X 0 * MvPowerSeries.X 1) +
                MvPowerSeries.C c * (MvPowerSeries.X 1) ^ 2} :
                Set (MvPowerSeries (Fin 2) F))))) ↔
      ∃ (a b c : F), b ^ 2 - 4 * a * c ≠ 0 ∧
        Nonempty
          ((MvPowerSeries (Fin n) F ⧸ I) ≃+*
            (MvPowerSeries (Fin 2) F ⧸
              Ideal.span ({MvPowerSeries.C a * (MvPowerSeries.X 0) ^ 2 +
                MvPowerSeries.C b * (MvPowerSeries.X 0 * MvPowerSeries.X 1) +
                MvPowerSeries.C c * (MvPowerSeries.X 1) ^ 2} :
                Set (MvPowerSeries (Fin 2) F))))) := by
  sorry

end MvPowerSeries
