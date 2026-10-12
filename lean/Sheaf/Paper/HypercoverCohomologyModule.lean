module

public import Sheaf.Paper.HypercoverCohomologyColimit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.Paper.FiniteSplitHypercoverRefinement
import Sheaf.Paper.HypercoverFreeResolution
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex

@[expose] public section

universe u₁

open CategoryTheory

namespace AlgebraicGeometry

/-- The constant-ring module part of hypercover cohomology comparison.
Source: Stacks Project, Tag 01H0; blueprint order 949.
The injective-resolution double-complex comparison in the module-sheaf category, together
with exactness of the forgetful functor and finite refinement lifting, establishes the
colimit universal property for every ring.
(blueprint: thm-weil-pbc-hypercover-cohomology-module-part) -/
theorem hypercover_cohomology_module_part (X : Scheme.{u₁}) [CompactSpace X]
    [QuasiSeparatedSpace X] (q : ℕ) (R : Type (u₁ + 1)) [Ring R] :
    FiniteSplitEtaleHypercover.IsCohomologyColimit (ModuleCat.{u₁ + 1} R) q
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u₁ + 1} R)) 0 ⋙
        Etale.cohomology (ModuleCat.{u₁ + 1} R) X (q : ℤ)) := by
  sorry

end AlgebraicGeometry
