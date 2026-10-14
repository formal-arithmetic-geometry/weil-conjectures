/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
public import Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnit

/-! # A single derived unit across a commutative direct-image square

Source: Stacks Project, Cohomology, Tags 08FE and 0D5T.
(blueprint: lem-pc-direct-image-square-single-unit-normalization).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian

-- Match the functor-category universe expression in the fixed comparison.
-- This avoids costly kernel conversion through the derived-functor definitions.
/-- Equality transport of one derived unit, before factoring it into two units.
Source: Stacks Project, Cohomology, Tags 08FE and 0D5T.
Proof: the pushforward composition isomorphisms are identities on sections.
The intervening pushforwardCongr is equality transport along the commutative-square
identity. Pass to complexes degreewise and then to the homotopy quotient, obtaining
that the displayed homotopy comparison is the equality map of the homotopy direct
image objects. The right-derived unit is a family of natural transformations in
the scheme morphism. Equality induction on the square identity gives that its
component followed by equality transport of the derived functors equals equality
transport of its source followed by the other component. Functoriality of Qh on
equality maps identifies that source transport with the displayed Qh.map.
This uses arbitrary homotopy objects; zero complexes and empty schemes are included.
The displayed derived-category structures are independent; no global choice of
a derived category for every scheme is required.
(blueprint: lem-pc-direct-image-square-single-unit-normalization). -/
theorem schemeDirectImageSquare_single_unit_normalization
    (X Y : Scheme.{u}) (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (U : Y.Opens)
    (K : HomotopyCategory
      (SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ U).toScheme.toRingedSpace))
      (ComplexShape.up ℤ)) :
    schemeMVCompositionUnit (h ⁻¹ᵁ U).ι h K ≫
        (eqToIso.{max (u + 1) w, max (u + 1) w} (congrArg schemeDerivedDirectImage
          (morphismRestrict_ι h U).symm)).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((schemeMVHomotopyOpenComposition h U).hom.app K) ≫
        schemeMVCompositionUnit (h ∣_ U) U.ι K := by sorry

end AlgebraicGeometry
