/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Affine cohomology coordinates for a supplied ordinary comparison

Source: Stacks Project, Tags 01I9, 06Z0 and 0AVW.
(blueprint: def-pc-affine-pushforward-comparison-coordinates). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

/-- The existing exact-tilde zero-map instance in displayed coordinates.
Source: Stacks Project, Tag 01I9.
(blueprint: def-pc-affine-pushforward-comparison-coordinates). -/
@[instance] theorem affinePushforwardTilde_preservesZero (A : Type u) [CommRing A] :
    (affinePushforwardTilde A).PreservesZeroMorphisms :=
  affineBaseChangeTilde_preservesZero A

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

end AlgebraicGeometry
