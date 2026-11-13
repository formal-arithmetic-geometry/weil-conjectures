/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.LiftToFinset
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import all WeilConjectures.CategoryTheory.CompactTestsRightAdjointCoproducts

/-!
# Finite cohomological dimension and coproducts of derived direct images

Source: Stacks Project, Tags 0F11 and 07K7.
-/

@[expose] public section

set_option autoImplicit false

universe w u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Finite cohomological dimension makes qcqs direct image with finite commutative
coefficients preserve all set-indexed coproducts on the ordinary unbounded derived categories.
There is no boundedness or constructibility restriction, and the index type may be empty.
Preservation means that the canonical comparison induced by the coprojections is invertible.

Source: Stacks Project, Tag 0F11, proof of (1), and Tag 07K7. -/
theorem rightDerivedLowerStar_preservesCoproducts_of_finite_dimension
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (f : U ⟶ T) [QuasiCompact f] [QuasiSeparated f]
    (c : ℕ)
    (hc : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (p : ℕ),
      c < p → IsZero (((lowerStar (ModuleCat.{u + 1} A) f).rightDerived p).obj M)) :
    ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) f) := by
  have hsmall (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I)
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor := by
    apply Functor.preservesColimitsOfShape_rightDerivedFunctor_of_rightDerived
      (lowerStar (ModuleCat.{u + 1} A) f) I c hc
    intro n
    have := preservesFilteredColimitsOfSize_higherDirectImage A f (n : ℤ)
    have : PreservesColimitsOfShape (Finset (Discrete I))
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerived n) :=
      preservesColimitsOfShape_of_natIso
        (Functor.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
          (lowerStar (ModuleCat.{u + 1} A) f) n)
    exact preservesColimitsOfShape_discrete_of_preservesColimitsOfShape_finset I _
  exact CategoryTheory.preservesCoproducts_of_small.{u + 1, w}
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor hsmall

end AlgebraicGeometry.Etale
