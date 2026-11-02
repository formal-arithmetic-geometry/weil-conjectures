/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernProjectivePolynomialValue
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier

/-! # Cartier root action on a restriction-zero ordinary class

(blueprint: lem-pur-chern-cartier-root-annihilation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace WeilConjectures.PurityFiniteSetting

/-- The positive Cartier-root action kills every ordinary class restricting to zero
on the divisor. No vector bundle, Chern polynomial, flag, or coefficient recurrence
occurs in this statement.

Source: Stacks Project, Cohomology Tags 0G75, 0G76 and 0G77; Tag 0FI5,
proposition-chern-class, the use of restriction-zero cup vanishing.
(blueprint: lem-pur-chern-cartier-root-annihilation).

Proof: the canonical Cartier Kummer arrow is supported on i and forgets to the
positive Kummer class of the dual ideal, O_X(Z). Its normalization fixes this
ordinary image at the displayed annihilating exponent. Regroup the ordered
positive finite Tate factors into a single Tate sheaf with its even shift, using
the canonical pure-tensor products and shift comparisons, and apply exact site
comparison and its single-functor comparison. These give the Hom coordinates of
the supported cup construction. Inverse-image naturality for the single, shift,
constant and twist comparisons carries the hypothesis hα to restriction zero in
those coordinates. Apply closed-supported cup vanishing to that class and the
canonical supported Cartier arrow, then forget support. The forgetting-support
square identifies the second factor with the displayed positive root. The first
factor is α. To identify this product with the raw tensor step, expand the cup's
unit diagonal and tensor map: tensor-comparison naturality moves the two Hom
arrows past the comparison maps, and their inverses cancel. Induct on the ordered
Tate factors to identify the output coefficient product; its pure-tensor maps
agree, and the even shifts contribute sign one. The inverse right-unit comparison
identifies the source diagonal. Hence, after the source and target isomorphisms,
the zero ordinary cup is exactly the displayed hyperplane step. Cancellation of
these isomorphisms gives zero in the original Hom group. -/
theorem ordinaryFiniteCartierRoot_annihilates
    (P : PurityFiniteSetting.{u}) {Z X : Scheme.{u}}
    (a : X ⟶ Spec (.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (i : Z ⟶ X) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (n : ℕ) (α : P.ordinaryFiniteCohomology X n)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (hα : P.ordinaryFiniteCohomologyPullback t i (P.diagonalExponent_isUnit a) n α = 0) :
    P.ordinaryFiniteHyperplaneStep X
      (P.ordinaryFiniteFlagRoot a i.ker.toModulesᵛ hI.isInvertible_dual_toModules) n α = 0 := by
  sorry

end WeilConjectures.PurityFiniteSetting
