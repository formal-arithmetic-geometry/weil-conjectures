/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LeftDerivedExactComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-!
# Canonical shifts and compositors of derived module functors

The pullback shifts are transported from exact termwise pullback by the canonical
counit comparison. The pushforward shifts are the published K-injective shifts.
All comparisons use the actual specified module-object functors and compositors.

## References

* Stacks Project, Tags 014X, 015F and 05SE
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical exact comparison for the specified K-flat module pullback. -/
def modulePullbackExactComparison :
    (moduleObjectDerivedPullback Λ f) ≅ (upperStar Λ f).mapDerivedCategory :=
  (upperStar Λ f).leftDerivedExactComparison
    (upperStar Λ f).leftDerivedFunctor (upperStar Λ f).leftDerivedFunctorCounit

/-- The specified integer shifts on derived module pullback, transported along `c_f`. -/
instance modulePullbackDerivedCommShift : (moduleObjectDerivedPullback Λ f).CommShift ℤ :=
  Functor.CommShift.ofIso (modulePullbackExactComparison Λ f).symm ℤ

/-- The published K-injective shifts on the named derived module pushforward. -/
instance modulePushforwardDerivedCommShift :
    (moduleObjectDerivedPushforward Λ f).CommShift ℤ :=
  inferInstanceAs ((lowerStar Λ f).rightDerivedFunctor.CommShift ℤ)

/-- The comparison on actual complexes, using localization and exact termwise pullback. -/
def modulePullbackComplexComparison :
    DerivedCategory.Q ⋙ (moduleObjectDerivedPullback Λ f) ≅
      (upperStar Λ f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  isoWhiskerLeft DerivedCategory.Q (modulePullbackExactComparison Λ f) ≪≫
    (upperStar Λ f).mapDerivedCategoryFactors

/-- Exactness with precisely the transported pullback shifts and the fixed K-injective
pushforward shifts; compatibility of `c_f` and the termwise comparison with every shift. -/
theorem module_derived_functors_exact_and_comparison_shifts :
    (moduleObjectDerivedPullback Λ f).IsTriangulated ∧
      (moduleObjectDerivedPushforward Λ f).IsTriangulated ∧
      NatTrans.CommShift (modulePullbackExactComparison Λ f).hom ℤ ∧
      NatTrans.CommShift (modulePullbackComplexComparison Λ f).hom ℤ := by
  have hs : NatTrans.CommShift (modulePullbackExactComparison Λ f).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (modulePullbackExactComparison Λ f).symm ℤ
  have hc : NatTrans.CommShift (modulePullbackExactComparison Λ f).hom ℤ :=
    NatTrans.CommShift.of_iso_inv (modulePullbackExactComparison Λ f).symm ℤ
  refine ⟨Functor.isTriangulated_of_iso (modulePullbackExactComparison Λ f).symm,
    ?_, hc, ?_⟩
  · exact inferInstanceAs ((lowerStar Λ f).rightDerivedFunctor.IsTriangulated)
  · change NatTrans.CommShift
      (whiskerLeft DerivedCategory.Q (modulePullbackExactComparison Λ f).hom ≫
        (upperStar Λ f).mapDerivedCategoryFactors.hom) ℤ
    infer_instance

variable (g : Y ⟶ Z)

/-- The specified derived compositor, with the named module-functor interfaces. -/
def modulePullbackDerivedCompositor :
    moduleObjectDerivedPullback Λ (f ≫ g) ≅
      moduleObjectDerivedPullback Λ g ⋙ moduleObjectDerivedPullback Λ f :=
  leftDerivedUpperStarComp Λ f g

end AlgebraicGeometry.ProEtale.CondensedRing
