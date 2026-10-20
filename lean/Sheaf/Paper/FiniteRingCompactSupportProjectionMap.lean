/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
Definition extracted by the maintainer L (2026-10-18).
Generic realization interface added by F6 (2026-10-21).
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Compact-support projection with arbitrary finite primary coefficients

Source: Weil blueprint, main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-compatibilities.proof.md`, Proof (3); Stacks Project, Tag 0F0G
(blueprint: def-sp-finite-ring-compact-support-projection-map).

The canonical coefficient realization changes only the presentation of module sheaves.
The projection arrow below is the published counit-defined compactification projection
transported by that realization, on the ordinary unbounded intrinsic derived categories.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

-- Use one ring structure in abstract coefficients and in their ULift specialization.
attribute [local instance 100001] CommRing.toRing

namespace AlgebraicGeometry.Scheme

/-- Realize a transformation of bifunctors through arbitrary functors.
This abstraction keeps the concrete coefficient realization out of whiskering reductions. -/
@[irreducible] noncomputable def sfRealizeCompactificationProjection
    {C₁ C₂ D₁ D₂ E E' : Type*}
    [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
    [Category* E] [Category* E']
    (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (Q : E ⥤ E')
    {P P' : D₁ ⥤ D₂ ⥤ E} (τ : P ⟶ P') :=
  (Functor.postcompose₂.obj Q).map
    ((((Functor.whiskeringLeft₂ E).obj F₁).obj F₂).map τ)

/-- Realization preserves invertibility of a component of a bifunctor transformation. -/
theorem isIso_sfRealizeCompactificationProjection_app_app
    {C₁ C₂ D₁ D₂ E E' : Type*}
    [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
    [Category* E] [Category* E']
    (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (Q : E ⥤ E')
    {P P' : D₁ ⥤ D₂ ⥤ E} (τ : P ⟶ P') (M : C₁) (K : C₂)
    [IsIso ((τ.app (F₁.obj M)).app (F₂.obj K))] :
    IsIso (((sfRealizeCompactificationProjection F₁ F₂ Q τ).app M).app K) := by
  unfold sfRealizeCompactificationProjection
  change IsIso (Q.map ((τ.app (F₁.obj M)).app (F₂.obj K)))
  infer_instance

/-- The standard abelian structure on fixed-scalar sheaves, stored with atomic inputs.
All derived interfaces below use this same structure rather than rebuilding its sheafification. -/
@[instance_reducible] noncomputable def sfFixedSheafAbelian
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    Abelian (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  inferInstance

attribute [local instance 100000] sfFixedSheafAbelian

/-- The existing small derived-category model for fixed scalar sheaves, stored once.
Keeping this data constant prevents nested proof abstraction from rebuilding the model. -/
@[instance_reducible] noncomputable def sfFixedDerivedCategoryModel
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    HasDerivedCategory.{u + 1} (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) :=
  inferInstance

attribute [local instance 100000] sfFixedDerivedCategoryModel

/-- The canonical derived realization, stored once with its inverse and coherence maps.
Its functor and inverse are exactly those obtained by deriving the original realization. -/
noncomputable def sfIntrinsicDerivedModuleEquivalence
    (T : Scheme.{u}) (R : Type u) [CommRing R] [Finite R] :
    DerivedCategory (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} R))) ≌
      proEtaleDerivedCategory T R :=
  (sfIntrinsicModuleEquivalence T R).mapDerivedCategory

/-- Source of the fixed-coefficient compactification projection, stored independently
of the transformation so later types do not repeat its derived tensor instances. -/
noncomputable def sfFixedCompactificationProjectionSource
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) ⥤
        DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) :=
  ProEtale.derivedTensorRightDerivedLowerShriek (ModuleCat.{u + 1} A) c

/-- Target of the fixed-coefficient compactification projection. -/
noncomputable def sfFixedCompactificationProjectionTarget
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) ⥤
        DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)) :=
  ProEtale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
    (ModuleCat.{u + 1} A) c

/-- The published fixed-coefficient projection, specialized once at the scalar ring. -/
noncomputable def sfFixedCompactificationProjection
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    sfFixedCompactificationProjectionSource A c ⟶
      sfFixedCompactificationProjectionTarget A c :=
  ProEtale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c

/-- The specified compact-support projection arrow in intrinsic constant-ring modules.
The fixed-scalar arrow is the counit-defined proper projection, followed by the inverse
open projection and the pullback-composition identification. Apply the canonical derived
realization after evaluating it on the inverse realizations of `M,K`. In particular this
is a natural transformation, with no chosen projection-formula isomorphism or Tor assumption.
Naturality in both arguments is inherited from the published natural transformation.
Source: blueprint Proof (3), tensor-map paragraph; Stacks Tag 0F0G
(blueprint: def-sp-finite-ring-compact-support-projection-map). -/
noncomputable def finiteRingCompactSupportProjection
    (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  sfRealizeCompactificationProjection
    (sfIntrinsicDerivedModuleEquivalence X R).inverse
    (sfIntrinsicDerivedModuleEquivalence Y R).inverse
    (sfIntrinsicDerivedModuleEquivalence Y R).functor
    (sfFixedCompactificationProjection (ULift.{u + 1, u} R) c)

end AlgebraicGeometry.Scheme
