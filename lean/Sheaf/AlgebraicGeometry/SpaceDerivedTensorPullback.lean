/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-! # Canonical derived tensor pullback on algebraic spaces

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 06YY and 08I6;
Derived Categories of Spaces, derived pullback (blueprint: def-sfb-space-derived-tensor-pullback).
The ordinary functor is transported through the already specified small-model equivalences.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w w'

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Tensor pullback in the existing equivalent small module categories.
Source: Stacks, Tag 03D7 (blueprint: def-sfb-space-derived-tensor-pullback). -/
def smallModuleTensorPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Y.SmallModules ⥤ X.SmallModules :=
  Y.smallModuleEquivalence.inverse ⋙ moduleTensorPullback f ⋙ X.smallModuleRestriction

/-- Tensor pullback and its small-model conjugate are additive.
Source: Stacks, Tag 03D7 (blueprint: def-sfb-space-derived-tensor-pullback).
Proof: tensor pullback is a left adjoint between additive categories, hence preserves
finite biproducts and addition. The model equivalences are additive for the same reason. -/
@[instance] theorem smallModuleTensorPullback_additive {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : (smallModuleTensorPullback f).Additive := by
  let : (moduleTensorPullback f).IsLeftAdjoint :=
    (moduleTensorAdjunction f).isLeftAdjoint
  have : (smallModuleTensorPullback f).IsLeftAdjoint := by
    dsimp only [smallModuleTensorPullback]
    infer_instance
  exact rightExactFunctor_le_additiveFunctor _ _ _ ((rightExactFunctor_iff _).2 inferInstance)

/-- The actual functor on cochain complexes followed by localization.
Source: Stacks, Tags 06YS, 06YY and 08I6 (blueprint: def-sfb-space-derived-tensor-pullback). -/
def smallTensorPullbackComplex {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasDerivedCategory.{w'} X.SmallModules] :
    CochainComplex Y.SmallModules ℤ ⥤ X.DerivedModules :=
  (smallModuleTensorPullback f).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

/-- The unbounded left derived tensor pullback exists with arbitrary localization size.
Source: Stacks, Cohomology on Sites, Tags 06YS, 06YY and 08I6
(blueprint: def-sfb-space-derived-tensor-pullback).
Proof: use K-flat resolutions of flat module sheaves on the small ringed models.
The exact inverse image followed by extension of scalars preserves quasi-isomorphisms
between these representatives. Localization of the resolving class gives the right Kan
extension of the displayed functor along Q. Changing the localization universe transports
the same universal property along the equivalence of localizations. -/
@[instance] theorem smallTensorPullbackComplex_hasLeftDerived {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [HasDerivedCategory.{w'} X.SmallModules] :
    (smallTensorPullbackComplex f).HasLeftDerivedFunctor
      (HomologicalComplex.quasiIso Y.SmallModules (.up ℤ)) := by
  sorry

/-- Canonical total left derived tensor pullback of the specified ordinary functor.
The right Kan extension retains its computation counit and is determined by its universal
property, rather than chosen from a mere existence of a functor or isomorphism.
Source: Stacks, Tags 06YS, 06YY and 08I6 (blueprint: def-sfb-space-derived-tensor-pullback). -/
def derivedTensorPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasDerivedCategory.{w} Y.SmallModules] [HasDerivedCategory.{w'} X.SmallModules] :
    Y.DerivedModules ⥤ X.DerivedModules :=
  (smallTensorPullbackComplex f).totalLeftDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso Y.SmallModules (.up ℤ))

end AlgebraicGeometry.AlgebraicSpace
