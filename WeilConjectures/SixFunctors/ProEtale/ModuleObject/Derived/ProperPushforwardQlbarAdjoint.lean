/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarLeftAdjoint

/-!
# A right adjoint to proper constructible pushforward with condensed Qlbar coefficients

The functor is the existing restriction of ambient derived direct image, with coefficient
ring `Profinite.padicAlgClRingObj`, whose sections take values in a finite subextension.

## Implementation details

This is the instance `isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`, obtained by
descent of the finite-coefficient adjunctions along the constructible cocones.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Proper direct image on bounded constructible condensed Qlbar complexes has a right adjoint. -/
theorem properPushforward_isLeftAdjoint_qlbar
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : Z ⟶ Y) [IsProper p.left] :
    (boundedConstructibleLowerStar ℓ p).IsLeftAdjoint :=
  isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj ℓ p

end AlgebraicGeometry.ProEtale.CondensedRing
