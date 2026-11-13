/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful

/-!
# Restriction of pro-etale extension by zero

Source: Weil blueprint, order 1848, the open-closed triangle unit calculation;
Stacks Project, Tags 03DI and 09AE (blueprint:
proposition-extension-zero-restriction-closed-subscheme--7).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The unit `M → j^* j_! M` is an isomorphism for the canonical open extension adjunction
on pro-etale module sheaves, in the intrinsic constant-coefficient presentation.
Source: Weil blueprint, order 1848; Stacks, Tags 03DI and 09AE
(blueprint: proposition-extension-zero-restriction-closed-subscheme--7).

Proof: the fixed-scalar extension-by-zero functor is fully faithful by
`ProEtale.fullyFaithfulOpenImmersionLowerShriek`. The intrinsic extension is its
composite with the inverse coefficient realization on `U` and coefficient realization
on `X`. Equivalences are fully faithful, as are composites of fully faithful functors.
Thus the left adjoint of the specified intrinsic adjunction is fully faithful, and
`CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful` makes its unit invertible. -/
theorem sfIntrinsicOpenUnit_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleRingModules U (proEtaleConstantRing U A)) :
    IsIso ((sfIntrinsicExtensionByZeroAdjunction j A).unit.app M) := by
  have : (sfIntrinsicExtensionByZero j A).Full := by
    dsimp only [sfIntrinsicExtensionByZero]
    infer_instance
  have : (sfIntrinsicExtensionByZero j A).Faithful := by
    dsimp only [sfIntrinsicExtensionByZero]
    infer_instance
  infer_instance

end AlgebraicGeometry.Scheme
