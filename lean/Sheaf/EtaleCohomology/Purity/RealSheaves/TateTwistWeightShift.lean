/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import Sheaf.Paper.IntrinsicCoefficientTwists
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.SfWeilSheafComplex
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.DeligneLaumon.Reduction.Weights
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.WeilSheaf.Triangle
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.WeilSheaf.Category
import Sheaf.Paper.PointFibreEquivalence
import Sheaf.Paper.LocalFrobeniusTrace
import Sheaf.LinearAlgebra.FrobeniusModuleWeights
import Sheaf.Paper.AdicPunctualWeights
import Sheaf.Paper.CartesianCoefficientTwists
import Sheaf.Paper.DerivedPullbackTensorIso
import WeilConjectures.WeilSheaf.TateTwistCohomology
import Sheaf.Paper.FrobeniusCoefficientTwistsCanonical
import Sheaf.Paper.TwistFrobeniusScalar

/-! # Weight shift under a Tate twist

Source: blueprint main-20261015, chapter sec-purity-real-sheaves, unit sk-p-real-rankin,
node lem-tw-tate-twist-weight-shift (blueprint: lem-tw-tate-twist-weight-shift).

The sheaf twist is tensoring with the published signed Tate line, constructed from roots
of unity, tensor powers and duals. The tensor product places the lisse Tate line first,
so it also applies to constructible sheaves which are not lisse.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- Tate twisting shifts punctual purity and mixed upper bounds by minus twice the twist.
Source: blueprint main-20261015, sk-p-real-rankin, lem-tw-tate-twist-weight-shift and its
five-step proof (blueprint: lem-tw-tate-twist-weight-shift); Deligne, Weil II, (1.2.5)--(1.2.7).

Proof: (1) On Spec k the Tate line has one-dimensional sections and geometric Frobenius
q^(-n), by lem-pur-twist-frobenius-scalar. A nonzero section trivializes it by
lem-weil-point-fibre-equivalence. Pull back using det-prop-sfb-cartesian-coefficients-twists;
the canonical Weil structure from def-weil-frobenius-coefficient-twists becomes q^(-n)
times the coefficient-unit structure, also for negative n.
(2) The tensor formula and natural pullback-tensor comparison of
lem-pur-derived-pullback-tensor-iso identify the twisted local Frobenius at a degree-m
closed point with q^(-mn) times the original operator: def-weil-local-frobenius-trace
iterates the Weil structure exactly m times, and point transport is coefficient-linear.
(3) Multiplication by the nonzero scalar c=q^(-mn) carries eigenvalues alpha to c*alpha;
the converse follows by multiplying by c inverse. This is the eigenvector definition of
def-weil-frobenius-module-weights and requires no semisimplicity.
(4) The residue cardinality is q_y=q^m. The coefficient isomorphism fixes rational numbers,
so multiplicativity of complex norm and the real-power laws give
|iota(q^(-mn)*alpha)| = q_y^(-n)*q_y^(w/2) = q_y^((w-2n)/2).
This is def-weil-punctual-weights and proves the pure clause, also for constructible pieces.
(5) Take the finite Weil-sheaf filtration witnessing mixedness. In the trivialization,
twisting keeps the underlying sheaves and maps and multiplies all Weil structures by the
same invertible scalar. Thus inclusions, kernels and quotients are preserved as Weil objects.
Each quotient is the twist of the original pure quotient, of weight u_j-2n <= w-2n by (4).
This filtration witnesses the mixed bound. The empty filtration covers the zero sheaf. -/
theorem tateTwist_weight_shift
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (ι : PadicAlgCl l ≃+* ℂ) (F : WeilSheaf k₀ l X) (n : ℤ) :
    (∀ {w : ℝ}, F.IsLisse → F.IsPunctuallyPureOfWeight ι.toRingHom w →
      IsPunctuallyPureOfWeight ι.toRingHom
        ((tateTwistSheaf k₀ l X n).tensorObj F (isLisse_tateTwistSheaf k₀ l X n))
        (w - 2 * n)) ∧
    (∀ {w : ℝ}, F.IsLisse → F.IsMixedOfWeightsAtMost ι.toRingHom w →
      IsMixedOfWeightsAtMost ι.toRingHom
        ((tateTwistSheaf k₀ l X n).tensorObj F (isLisse_tateTwistSheaf k₀ l X n))
        (w - 2 * n)) := by
  sorry

end AlgebraicGeometry.WeilSheaf
