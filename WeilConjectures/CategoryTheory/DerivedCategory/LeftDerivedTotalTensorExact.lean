/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedTotalTensor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-!
# The left derived functor of an exact functor

Source: blueprint main-20261015, `sec-proetale-coefficients`,
`sk-def-sfb-derived-categories`, `def-sfb-left-derived-exact`
(blueprint: def-sfb-left-derived-exact).

The canonical comparison uses the recorded total-tensor left derived functor and
Mathlib's uniqueness isomorphism, with no additional graded-tensor hypotheses.

## Main definitions

* `leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory`: the canonical comparison.
* `leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory_hom_fac`: its counit compatibility.
-/

@[expose] public section

universe uC vC uD vD wC wD

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C] [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The canonical isomorphism from the left derived functor of an exact functor to
its termwise functor on derived categories.
Source: blueprint main-20261015, `def-sfb-left-derived-exact`, statement and proof
(blueprint: def-sfb-left-derived-exact).

Exactness supplies preservation of K-flat quasi-isomorphisms by the recorded
`def-sfb-preserves-kflat-quasi-iso` declaration. The factorization isomorphism
`mapDerivedCategoryFactorsh` makes the termwise functor itself left derived.
The recorded `def-sfb-left-derived-functor` universal property and Mathlib's
`leftDerivedUnique` then give the canonical comparison of the two counited functors. -/
noncomputable def leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory :
    F.leftDerivedFunctorFromTotalTensor
        (hF := F.preservesTotalTensorKFlatQuasiIso_of_exact) ≅ F.mapDerivedCategory :=
  letI := F.preservesTotalTensorKFlatQuasiIso_of_exact
  letI := F.isLeftDerivedFunctor_leftDerivedFunctorFromTotalTensor
  letI := isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    F.mapDerivedCategory F.mapDerivedCategoryFactorsh
  leftDerivedUnique F.mapDerivedCategory F.leftDerivedFunctorFromTotalTensor
    F.leftDerivedFunctorFromTotalTensorCounit F.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

/-- The canonical comparison respects the canonical counits.
Source: blueprint main-20261015, `def-sfb-left-derived-exact`, proof's uniqueness clause
(blueprint: def-sfb-left-derived-exact).

Proof: exactness makes the termwise factorization an invertible counit, hence a left
derived counit, and the recorded left derived functor has its universal counit.
The comparison is `leftDerivedUnique` for these two counits. Its factorization law
is precisely the displayed equation, which characterizes the canonical comparison. -/
theorem leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory_hom_fac :
    whiskerLeft DerivedCategory.Qh F.leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory.hom ≫
        F.mapDerivedCategoryFactorsh.hom =
      F.leftDerivedFunctorFromTotalTensorCounit
        (hF := F.preservesTotalTensorKFlatQuasiIso_of_exact) := by
  simp [leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory]

end CategoryTheory.Functor
