/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module
public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
/-! # Canonical affine algebra module adjunction component

Source: Stacks Project, Tags 0AVW and 01SB. -/

@[expose] public section

noncomputable section
universe v
open CategoryTheory
namespace AlgebraicGeometry
/-- The canonical affine algebra adjunction component.
Source: Stacks Project, Tags 0AVW and 01SB.
(blueprint: new-affine-algebra-module-unit-iso).

Proof: Identify the canonical left adjoint with tensor pullback for g by its Hom adjunction.
Associativity identifies this pullback with the two tensor operations in the affine module
correspondence. Its unit is beta: both are adjoint to the tensor unit s mapped to s tensor 1.
The correspondence proves beta invertible on quasi-coherent algebra modules. Transport the unit
across the unique adjunction-compatible isomorphism of left adjoints; its image under G is
invertible too. The same tensor calculation covers zero rings and modules.
-/
theorem affine_algebra_module_adjunction_unit_iso
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [(RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).IsRightAdjoint] :
    ∀ M : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)),
      M.IsQuasicoherent → IsIso
        ((Adjunction.ofIsRightAdjoint
          (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))).unit.app M) := by sorry
end AlgebraicGeometry
