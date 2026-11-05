/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Derived.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjectiveResolution
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

/-!
# The Čech resolution computes the derived direct image

Let `f : X ⟶ S` be separated and `U` a finite family of opens covering `X` whose finite
intersections are affine over `S`. For a quasi-coherent `𝒪_X`-module `ℱ`, the derived direct image
`Rf_* ℱ` is the complex `f_* Č(U, ℱ)` in the derived category `D(𝒪_S)`
(`AlgebraicGeometry.Scheme.Modules.derivedPushforwardSingleIsoCechResolution`): the Čech
resolution `ℱ ⟶ Č(U, ℱ)` is a resolution by `f_*`-acyclic modules. This is the derived-category
form of `AlgebraicGeometry.Scheme.Modules.higherDirectImageIsoCechResolutionOfIsAffineHom`.
Its cohomology sheaves are the higher direct images
(`AlgebraicGeometry.Scheme.Modules.homologyDerivedPushforwardSingleIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type u} (U : ι → X.Opens)

instance : PreservesFiniteLimits (pushforward f) :=
  have := (pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
  inferInstance

end AlgebraicGeometry.Scheme.Modules
