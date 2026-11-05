/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import WeilConjectures.Algebra.Homology.AffineBaseChangeIntoPullback
public import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde

/-! # Explicit coordinates for affine base-change cohomology

Source: Stacks Project, Tags 0DJ8, 06Y6 and 01I9.
(blueprint: def-pc-affine-base-change-tilde-coordinates). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

/-- Exact tilde preserves zero morphisms. Source: Stacks, Tag 01I9.
(blueprint: def-pc-affine-base-change-tilde-coordinates). -/
@[instance] theorem affineBaseChangeTilde_preservesZero (A : Type u) [CommRing A] :
    (@id (ModuleCat.{u} A ⥤ SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace))
        (tilde.functor (.of A))).PreservesZeroMorphisms :=
  ⟨fun _ _ ↦ tilde.map_zero⟩

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

end AlgebraicGeometry
