/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M6
-/
module

public import Sheaf.Paper.ClopenStrictSystemComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # A finite-coefficient inverse on a pure-dimensional smooth source

Source: blueprint smooth purity, thm-pur-cohomological-smoothness, first paragraph;
finite-clopen dualizing inverse assembly, Step 4.
(blueprint: lem-pur-smooth-finite-dualizing-inverse).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- A smooth exceptional image of the coefficient unit of pure relative dimension
has a two-sided finite-Tor constructible inverse in the actual intrinsic coefficient
category. There is no choice of a trivialization or Tate orientation.

Source: blueprint thm-pur-cohomological-smoothness, first paragraph, and Step 4 of
lem-pur-varying-dimension-dualizing-inverse.
(blueprint: lem-pur-smooth-finite-dualizing-inverse).

Proof: apply finite_setting_comparison_hypotheses with the setting whose level is
n+1. It supplies Noetherianity of the target, compactifiability, finiteness of the
coefficient ring, and an invertible positive annihilator. Smooth tensor duality
identifies the etale exceptional image of the unit with L[2d], where L is etale
locally a free rank-one coefficient module. Apply shifted_line_site_inverse to L
with shift 2d. Its dual shifted by -2d gives both inverse evaluations and is
bounded constructible of finite Tor amplitude, as is L[2d]. The finite exceptional
functor is the specified etale exceptional functor transported through the two
site comparisons. The comparison adjunction unit on the etale coefficient unit
identifies its input with that unit, so its value is the comparison pullback of
L[2d]. Transport the inverse and both evaluations through the intrinsic module
realization equivalence. Its tensor comparison, and uniqueness of derived tensor
on K-flat representatives, identify this tensor with finiteIntrinsicDerivedTensor;
the same realization identifies the unit with finiteConstantCoefficientObject.
Constructibility and the Tor tests are invariant under these equivalences, giving
the recorded finiteTorConstructible predicates. This also covers the empty source:
the module category there is zero, and the coefficient unit is its own inverse. -/
theorem smooth_finite_dualizing_inverse (P : PurityFiniteSetting.{u})
    (X Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d n : ℕ) [SmoothOfRelativeDimension d g] :
    let omega := (clopenFiniteExceptional P P.extension X Y g n).obj
      (finiteConstantCoefficientObject P.coefficients.l P.extension Y.left n)
    finiteTorConstructible P.coefficients.l P.extension (n + 1) (Nat.succ_pos n)
        X.left omega ∧
      ∃ Q, finiteTorConstructible P.coefficients.l P.extension (n + 1) (Nat.succ_pos n)
          X.left Q ∧
        Nonempty ((finiteIntrinsicDerivedTensor P.coefficients.l P.extension X.left n).obj
          (omega, Q) ≅ finiteConstantCoefficientObject P.coefficients.l P.extension X.left n) ∧
        Nonempty ((finiteIntrinsicDerivedTensor P.coefficients.l P.extension X.left n).obj
          (Q, omega) ≅ finiteConstantCoefficientObject P.coefficients.l P.extension X.left n) := by
  sorry

end WeilConjectures.PurityFiniteSetting
