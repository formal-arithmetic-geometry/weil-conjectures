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
(blueprint: new-affine-algebra-module-counit-iso).

Proof: Identify the canonical left adjoint with tensor pullback for g by its Hom adjunction. Tensor
associativity identifies it with the two operations in the affine module correspondence. Its
counit is alpha: on pure tensors the evaluation sends a tensor s to a times s, uniquely by the
tensor universal property. The correspondence proves alpha invertible on quasi-coherent O_X-
modules. Transport it across the adjunction-compatible isomorphism of left adjoints. No
surjectivity of f is used; empty schemes and zero modules satisfy the claim.
-/
theorem affine_algebra_module_adjunction_counit_iso
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [(RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).IsRightAdjoint] :
    ∀ K : SheafOfModules.{v} (moduleRings X.toRingedSpace),
      K.IsQuasicoherent → IsIso
        ((Adjunction.ofIsRightAdjoint
          (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))).counit.app K) := by sorry
end AlgebraicGeometry
