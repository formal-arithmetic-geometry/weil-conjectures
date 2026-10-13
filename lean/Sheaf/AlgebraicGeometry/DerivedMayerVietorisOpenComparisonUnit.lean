/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # Compatibility of the canonical single-open direct-image comparison

Source: Stacks Project, Tags 08FE, 0D5T and 08BV.
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

/-- Direct image and the canonical open comparison carry a single restriction unit
on X to the corresponding restriction unit on Y. No cover or triangle is involved.
Source: Stacks Project, Tag 08FE, proof on K-injective representatives; Tag 0D5T,
canonical composition of derived direct images; Tag 08BV, first proof paragraph.

Proof: Represent E by a K-injective I. Restriction to h⁻¹U is K-injective.
Expand schemeMVOpenComparison into the two normalized composition comparisons,
the equality (h restricted to U) followed by the open inclusion = the inverse-image
inclusion followed by h, and the inverse restriction/direct-image comparison.
The right-derived unit equation characterizing each composition comparison identifies
this expansion on I with the localization of the sectionwise direct-image identity.
That identity carries the restriction unit to the restriction unit: both send a
section on an open W of Y to its restriction on h⁻¹(W ∩ U). Use
schemeOpenModuleImageComplexComparison_unit on X and Y to identify these localized
units with schemeMVAdjunction units. The factorization equations of the exact
restriction localization comparison and the right-derived computation comparison
cancel the intermediate identifications. Finally transport the equality from Q(I)
to E along schemeMVResolutionIso, using unit naturality and naturality of each
comparison. This argument also applies to U empty or U top and requires no cover.
(blueprint: lem-pc-derived-mayer-vietoris-open-comparison-unit). -/
theorem schemeMVOpenComparison_unit
    (X Y : Scheme.{u}) (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (U : Y.Opens) (E : schemeDerivedCategory X) :
    (schemeDerivedDirectImage h).map ((schemeMVAdjunction X (h ⁻¹ᵁ U)).unit.app E) ≫
        (schemeMVOpenComparison h U E).hom =
      (schemeMVAdjunction Y U).unit.app ((schemeDerivedDirectImage h).obj E) := by
  sorry

end AlgebraicGeometry
