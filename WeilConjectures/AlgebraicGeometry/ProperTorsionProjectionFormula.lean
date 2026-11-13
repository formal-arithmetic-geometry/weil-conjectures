/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula

/-!
# The proper projection formula with torsion coefficients

## References

* [Stacks, Tag 0F0G] (Étale Cohomology)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- For a proper morphism and a torsion commutative coefficient ring, the canonical
projection-formula map is invertible on arbitrary unbounded complexes.
(Stacks, Tag 0F0G) -/
theorem isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
    (Λ : Type (u + 1)) [CommRing Λ] (hΛ : IsAddTorsion Λ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (E : DerivedCategoryModule Λ X) (K : DerivedCategoryModule Λ Y) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app E).app K) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_isProper Λ hΛ f
  infer_instance

end AlgebraicGeometry.Etale
