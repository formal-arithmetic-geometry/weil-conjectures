/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Derived tensor and exact restriction

Source: Stacks Project, Tag 08DX, proof of (1).
(blueprint: lem-pc-derived-tensor-open-restriction-universes).
-/

@[expose] public section

universe u w wO

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Derived tensor commutes with exact open restriction, allowing independent
localization universes. Source: Stacks Project, Tag 08DX, proof of (1).
Proof: choose K-flat representatives of the first factor. Open restriction is exact,
preserves K-flatness and commutes with the sheaf tensor and the coproducts in
unbounded totalization. The restricted total tensor therefore computes both sides.
The localization comparison transports this calculation between the independently
chosen derived categories. This is natural in both factors, and includes empty opens.
(blueprint: lem-pc-derived-tensor-open-restriction-universes). -/
theorem derivedTensor_openRestriction_iso_universes (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wO} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (E F : schemeDerivedCategory X) :
    Nonempty
      ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj (E ⊗ F) ≅
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj E ⊗
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj F) := by
  sorry

end AlgebraicGeometry
