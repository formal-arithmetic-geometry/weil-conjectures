/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FlatRingedDiagramInput.FlatRingedDiagramRestrictionDefs

/-!
# Derived comparison structures for flat coefficient restriction

Source: Stacks Project, Derived Categories, Tags 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
namespace FlatRingedDiagramInput

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}
  (x : FlatRingedDiagramInput K H) (J : Type u) [SmallCategory J]
  [HasDerivedCategory.{w} (x.diagramsRU J)]
  [HasDerivedCategory.{w} (x.diagramsSU J)]
  [HasDerivedCategory.{w} (x.diagramsRV J)]
  [HasDerivedCategory.{w} (x.diagramsSV J)]
/-- The comparison functors and their localization factors.
Source: Stacks 03D3, 0FND and 0DVC
(blueprint: def-weil-pbc-flat-ringed-diagram-comparisons). -/
structure DerivedRestrictionComparisonMaps
    (LR : derivedRV x J ⥤ derivedRU x J)
    (FR : derivedRU x J ⥤ derivedRV x J)
    (LS : derivedSV x J ⥤ derivedSU x J)
    (FS : derivedSU x J ⥤ derivedSV x J) where
  b0 : x.inverseS J ⋙ x.restrictU J ≅ x.restrictV J ⋙ x.inverseR J
  d0 : x.directS J ⋙ x.restrictV J ≅ x.restrictU J ⋙ x.directR J
  rU : derivedSU x J ⥤ derivedRU x J
  rV : derivedSV x J ⥤ derivedRV x J
  qU : DerivedCategory.Q ⋙ rU ≅ restrictUComplex x J ⋙ DerivedCategory.Q
  qV : DerivedCategory.Q ⋙ rV ≅ restrictVComplex x J ⋙ DerivedCategory.Q
  b : LS ⋙ rU ≅ rV ⋙ LR
  d : FS ⋙ rV ≅ rU ⋙ FR


end FlatRingedDiagramInput
end CategoryTheory
