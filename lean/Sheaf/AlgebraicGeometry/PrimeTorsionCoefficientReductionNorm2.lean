/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReductionComplexesCore

/-!
# Derived coefficient tensor isomorphism type

Source: Stacks Project, Tags 03EK, 06YU and 0F1J
(blueprint: def-kun-prime-coefficient-iso).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
/-- Type of coefficient tensor isomorphism.
Source: Stacks, Tag 0F1J (blueprint: def-kun-prime-coefficient-iso). -/
abbrev PrimeTensorCoefficientIso (φ : A →+* B) (V : Scheme.{u})
    (D : DerivedCategoryModule A V) (D' : DerivedCategoryModule B V) :=
  (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ ⋙
      (derivedTensor (ModuleCat.{u + 1} A) V).obj D) ≅
    ((derivedTensor (ModuleCat.{u + 1} B) V).obj D' ⋙
      Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)

end AlgebraicGeometry.Etale
