/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientOperationEncoding
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartEncoding
import WeilConjectures.CategoryTheory.SixFunctors.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison

/-! # Tensor and pullback comparisons for normalized finite coefficients

Only left derived pullbacks and the native derived tensor bifunctors occur in the
comparison asserted here. No projection morphism or direct-image property is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.Functor

section DerivedSquare

universe a b c d

variable {A : Type a} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
  {B : Type b} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalClosed B]
  [MonoidalPreadditive B] [BraidedCategory B] [Abelian.HasFunctorialFlatResolution B]
  {C : Type c} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
  {D : Type d} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D] [MonoidalClosed D]
  [MonoidalPreadditive D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F₁ : A ⥤ B) [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₁.PreservesFlat] [F₁.IsLeftAdjoint] [F₁.Monoidal]
  (F₂ : B ⥤ D) [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [F₂.PreservesFlat] [F₂.IsLeftAdjoint] [F₂.Monoidal]
  (G₁ : A ⥤ C) [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₁.PreservesFlat] [G₁.IsLeftAdjoint] [G₁.Monoidal]
  (G₂ : C ⥤ D) [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [G₂.PreservesFlat] [G₂.IsLeftAdjoint] [G₂.Monoidal]
  (τ : G₁ ⋙ G₂ ≅ F₁ ⋙ F₂) [NatTrans.IsMonoidal τ.hom]

end DerivedSquare

namespace CategoryTheory.Adjunction

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale

/-- The native internal projection data, with resolving constructions behind one bundle.
Source: the internal derived geometric adjunction and tensor comparison
(blueprint: lem-sfb-finite-coefficient-tensor-pullback-encoding). -/
@[irreducible] def internalProjectionContext
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Adjunction.ProjectionContext
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj R X)))
      (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj R Y))) where
  pull := _
  push := _
  adj := CondensedRing.derivedUpperStarLowerStarAdjunction R p
  tensorC := _
  tensorD := _
  comparison := CondensedRing.leftDerivedUpperStarTensor R p

/-- The native ordinary projection data in the fixed scalar universe.
Source: the ordinary derived geometric adjunction and tensor comparison
(blueprint: lem-sfb-finite-coefficient-tensor-pullback-encoding). -/
@[irreducible] def ordinaryProjectionContext
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Adjunction.ProjectionContext
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
      (DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) where
  pull := _
  push := _
  adj := ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p
  tensorC := _
  tensorD := _
  comparison := ProEtale.leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) p

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

open Scheme

attribute [local instance 20000] sheafBraidedCategory
attribute [local instance 2000] Mod.monoidalCategory Mod.monoidalClosed
attribute [local irreducible] Mod.monoidalCategoryStruct Mod.monoidalCategory Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit Functor.mapDerivedCategory
  DerivedCategory.Qh Functor.leftDerivedFunctorCompNatIso
  Functor.leftDerivedFunctorIsoMapDerivedCategory Functor.mapDerivedCategoryCompIso
  CondensedRing.leftDerivedUpperStarTensor
  ProEtale.leftDerivedUpperStarTensorComparison Functor.leftDerivedTensorComparison

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
variable {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R]

-- Cache the tensor hypotheses before instantiating the generic derived-square theorem.

attribute [local instance] internalBraided

attribute [local instance] internalClosed

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
