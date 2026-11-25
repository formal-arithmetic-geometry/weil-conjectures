/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Analytically unramified local rings and prime ideals

## Main definitions

* `IsAnalyticallyUnramified`: the maximal-ideal-adic completion is reduced.
* `Ideal.IsAnalyticallyUnramified`: the quotient by a prime ideal is analytically unramified.

## References

* Stacks Project, Algebra, Definition 032X.
-/

@[expose] public section

universe u

/-- A Noetherian local ring is analytically unramified when its completion with respect to
its maximal ideal is reduced. -/
def IsAnalyticallyUnramified (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : Prop :=
  IsReduced (AdicCompletion (IsLocalRing.maximalIdeal R) R)

namespace Ideal

/-- A prime ideal `p` of a Noetherian local ring `R` is analytically unramified when the
completion of `R ⧸ p` with respect to the image of the maximal ideal of `R` is reduced. -/
def IsAnalyticallyUnramified {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (p : Ideal R) : Prop :=
  p.IsPrime ∧
    IsReduced (AdicCompletion ((IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk p))
      (R ⧸ p))

end Ideal
