/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q160
-/
module

public import Sheaf.Paper.OrgogozoInductionData

/-! # Ordinary multiple points

Source: Temkin, Stable Modification of Relative Curves, Appendix B, printed pp. 56–57;
Stacks Project, Curves, Section multicross, Tags 0C1U and 0C1W.
(blueprint: def-trf-ordinary-multiple-point).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The complete coordinate-axes algebra on `n` branches, including the one-axis case.
Source: Temkin, Appendix B, ordinary n-fold points, printed p. 57;
Stacks Project, Curves, equation multicross, Tag 0C1U.
(blueprint: def-trf-ordinary-multiple-point). -/
abbrev ordinaryMultiplePointRing (k : Type u) [Field k] (n : ℕ) :=
  MvPowerSeries (Fin n) k ⧸ Ideal.span
    {g : MvPowerSeries (Fin n) k |
      ∃ i j : Fin n, i ≠ j ∧ g = MvPowerSeries.X i * MvPowerSeries.X j}

/-- An ordinary `n`-fold point has the coordinate-axes completed local ring, with its
specified ground-field scalars. The displayed compatibility is exactly a k-algebra
isomorphism, expressed without choosing a second algebra structure on the stalk.
Source: Temkin, Appendix B, printed p. 57; Stacks Project, Curves, Tag 0C1W.
(blueprint: def-trf-ordinary-multiple-point). -/
def IsOrdinaryMultiplePoint {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (x : X) (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃+* ordinaryMultiplePointRing k n,
    ∀ a : k, e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) (Orgogozo.localScalar p x a)) =
        Ideal.Quotient.mk _ (MvPowerSeries.C a)

end AlgebraicGeometry
