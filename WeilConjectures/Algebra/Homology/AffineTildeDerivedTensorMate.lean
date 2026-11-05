/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentative
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparison
public import WeilConjectures.Algebra.Homology.AffineTildeTensorOrdinaryExchange

/-! # The derived affine tensor mate before taking homology

Source: Stacks Project, Tags 0DJ8, 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-derived-tensor-mate). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

variable (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
  [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
  [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
  (M : CochainComplex (ModuleCat.{u} A) ℤ)
  (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D)

attribute [local irreducible] tilde Functor.mapDerivedCategory affineTildePushforwardComparison
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit Scheme.Modules.tensorPullback
  affineBaseChangeTildeRepresentativeIso affineTildeTensorOrdinarySourceIso
  schemeDerivedBaseChangeMap affineTildeTensorDerivedCounit affineTildeTensorOrdinaryTargetMap
  affineTildeDerivedTensorToPushforward

end AlgebraicGeometry
