/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions



/-! # The single complex of coefficients restricted from W

## References

* Stacks Project, Tags 03Q8 and 09Z1
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The restricted coefficient sheaf placed in degree zero, shared by raw pullback
and its comparison. -/
noncomputable def higherDirectImageRawOverComplex
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (B : Over W) :
    DerivedCategory.Plus (Sheaf B.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G)

/-- The shared complex is the original restricted single complex. -/
theorem higherDirectImageRawOverComplex_eq
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (B : Over W) :
    higherDirectImageRawOverComplex Λ G B =
  (DerivedCategory.Plus.singleFunctor _ 0).obj (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G) := by rfl

end AlgebraicGeometry.Etale
