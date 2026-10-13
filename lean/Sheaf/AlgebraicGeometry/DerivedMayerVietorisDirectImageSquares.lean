/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # DerivedMayerVietorisDirectImageSquares

Source: Stacks Project, Cohomology, Tags 08BV and 0D5T; Derived Categories of Schemes,
Tag 0DJ9 (blueprint: lem-pc-derived-mayer-vietoris-direct-image-squares).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian

/-- The recorded comparisons commute with the first two arrows of the explicit triangles.
Source: Stacks Tags 0D5T and 0DJ9
(blueprint: lem-pc-derived-mayer-vietoris-direct-image-squares).

Proof:
1. Compute both sides on the fixed K-injective representative of E. Restriction to an
   inverse-image open is K-injective. Direct image and open restriction are identified
   sectionwise, and the composition comparison identifies their two pushforwards.
2. The sectionwise identity carries the unit on X to the unit on Y. Combining the
   two open squares with the localization biproduct comparison gives the first square.
3. For the second square, the same sectionwise identity commutes with the two nested
   restriction maps to the intersection. The mate formula for the derived restriction
   maps transports this identity to the derived category. Additivity preserves their
   difference, and the biproduct comparison assembles the second square.
4. Transport from the representative to E by the resolution isomorphism. Naturality
   of the functor comparisons and of units and restrictions gives the stated equations.
-/
theorem schemeMV_directImage_squares
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    (hcover : U ⊔ V = ⊤)
    (hcover' : (h ⁻¹ᵁ U) ⊔ (h ⁻¹ᵁ V) = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) :
    (schemeMVImageTriangle h
      (schemeMVTriangle X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) hcover' E)).mor₁ ≫
        (schemeMVMiddleComparison h U V E).hom =
      (schemeMVTriangle Y U V hcover ((schemeDerivedDirectImage h).obj E)).mor₁ ∧
    (schemeMVImageTriangle h
      (schemeMVTriangle X (h ⁻¹ᵁ U) (h ⁻¹ᵁ V) hcover' E)).mor₂ ≫
        (schemeMVOpenComparison h (U ⊓ V) E).hom =
      (schemeMVMiddleComparison h U V E).hom ≫
        (schemeMVTriangle Y U V hcover ((schemeDerivedDirectImage h).obj E)).mor₂ := by
  sorry

end AlgebraicGeometry
