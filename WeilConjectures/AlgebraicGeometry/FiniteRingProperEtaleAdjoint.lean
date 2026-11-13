/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.AlgebraicGeometry.FiniteRingProperEtaleCoproducts
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Proper étale pushforward with finite ring coefficients

## Implementation details

The coefficient ring need not be commutative. The upstream instance requires `CommRing`, so it
cannot supply the noncommutative instances needed here.

## References

* Stacks Project, Tags 0F0D and 0F5Y.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

private theorem finiteRing_brown
    (Λ : Type (u + 1)) [Ring Λ]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (hcoprod : ∀ I : Type (u + 1),
      CategoryTheory.Limits.PreservesColimitsOfShape (Discrete I)
        (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor) :
    (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor.IsLeftAdjoint := by
  let : Limits.HasCoproducts.{u + 1}
      (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
    derived_hasCoproducts
  let : Limits.HasCoproducts.{u + 1}
      (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
    derived_hasCoproducts
  exact grothendieckDerived_hasRightAdjoint _ hcoprod

/-- Proper pushforward on unbounded derived categories of étale sheaves of modules over
any finite ring has a right adjoint (Stacks, Tags 0F0D, 0F5Y). -/
theorem finiteRing_isLeftAdjoint_rightDerivedLowerStar_of_isProper
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) [IsProper g] :
    (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctor.IsLeftAdjoint := by
  exact finiteRing_brown Λ g (finiteRing_preservesCoproducts_rightDerivedLowerStar Λ g)

end AlgebraicGeometry.Etale
