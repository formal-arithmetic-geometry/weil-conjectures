/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedDirectImageSplitTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Naturality component for the shifted K-injective comparison

Source: Stacks Project, Tag 079V.
(blueprint: lem-pc-direct-image-kinjective-comparison-shift-aux)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxSynthPendingDepth 8

noncomputable section
namespace AlgebraicGeometry.RingedSpace

/-- The comparison after applying the inverse derived shift map is the shifted
comparison followed by the inverse localized shift identification.
Source: Stacks Project, Tag 079V.
(blueprint: lem-pc-direct-image-kinjective-comparison-shift-aux)

This is the component identity obtained by transporting the right-derived unit
along the K-injective equivalence.  Naturality of that unit with respect to the
canonical shift map gives the displayed equality; the termwise direct-image
shift comparison is then the final inverse identification. -/
theorem derivedModuleDirectImageKInjectiveIso_shift_aux
    {X Y : RingedSpace.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y))]
    (g : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [K.IsKInjective] :
    (derivedModuleDirectImage g).map
        ((DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app K) ≫
      (derivedModuleDirectImageKInjectiveIso g (K⟦(1 : ℤ)⟧)).hom =
    ((derivedModuleDirectImage g).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Q.obj K) ≫
      (derivedModuleDirectImageKInjectiveIso g K).hom⟦(1 : ℤ)⟧' ≫
      (moduleDirectImageLocalizedShiftIso g K).inv := by sorry

end AlgebraicGeometry.RingedSpace
