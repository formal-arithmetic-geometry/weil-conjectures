/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates
public import WeilConjectures.Algebra.Homology.AffineTildePushforwardCohomologyNormalization

/-! # Normalized affine pushforward cohomology

Compatibility interface for the complete adopted normalization implementation,
retaining the legacy associated-sheaf abbreviation.

Source: Stacks Project, Tags 0AVW, 08D4 and 0DJ8.
(blueprint: lem-pc-affine-tilde-pushforward-cohomology-normalization). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry

/-- Associated sheaf, with its scheme-module category displayed explicitly.
Source: Stacks, Tag 01I9.
(blueprint: lem-pc-affine-tilde-pushforward-cohomology-normalization). -/
abbrev affineTildeFunctor (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) := affinePushforwardTilde A

/-- Instance bridge for the displayed affine tilde abbreviation, reusing exact tilde's
existing zero-map instance. Source: Stacks, Tag 01I9.
(blueprint: lem-pc-affine-tilde-pushforward-cohomology-normalization). -/
@[instance] theorem affineTildeFunctor_preservesZero (A : Type u) [CommRing A] :
    (affineTildeFunctor A).PreservesZeroMorphisms :=
  affinePushforwardTilde_preservesZero A

end AlgebraicGeometry
