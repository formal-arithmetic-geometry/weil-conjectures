/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRealization
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-!
# Coefficient compatibility of the actual projection mate

Source: blueprint main-20261015, sk-thm-sfb-proper-base-change-rational.proof.md,
paragraph (3), projection on integral-model pairs before invertibility
(blueprint: lem-sfb-coefficient-projection-square).
-/

@[expose] public noncomputable section

set_option autoImplicit false

-- Keep the internal-Hom construction and the inverse image from the point opaque.
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open CategoryTheory.Abelian
open scoped CategoryTheory.Obj

universe v u₁ u₂ u₃ u₄
namespace CategoryTheory.Adjunction
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {A : Type u₁} {B : Type u₂} {B' : Type u₃} {C : Type u₄}
  [Category.{v} A] [Category.{v} B] [Category.{v} B'] [Category.{v} C]
  [Abelian A] [Abelian B] [Abelian B'] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions B']
  [Abelian.HasKInjectiveResolutions C]
  {F₁ : A ⥤ B} {F₂ : B ⥤ C} {G₁ : A ⥤ B'} {G₂ : B' ⥤ C}
  {U₁ : B ⥤ A} {U₂ : C ⥤ B} {V₁ : B' ⥤ A} {V₂ : C ⥤ B'}
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
  [U₁.Additive] [U₂.Additive] [V₁.Additive] [V₂.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
  [U₂.PreservesKInjectiveComplexes] [V₂.PreservesKInjectiveComplexes]
  (a₁ : F₁ ⊣ U₁) (a₂ : F₂ ⊣ U₂) (b₁ : G₁ ⊣ V₁) (b₂ : G₂ ⊣ V₂)

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [CategoryTheory.Abelian.HasKInjectiveResolutions D]
  (f : C ⥤ D) (g : D ⥤ C) [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]

variable [PreservesFiniteLimits f] [PreservesFiniteColimits f]
end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction
variable {A B B' C : Type*} [Category A] [Category B] [Category B'] [Category C]
  {F₁ : A ⥤ B} {F₂ : B ⥤ C} {G₁ : A ⥤ B'} {G₂ : B' ⥤ C}
  {U₁ : B ⥤ A} {U₂ : C ⥤ B} {V₁ : B' ⥤ A} {V₂ : C ⥤ B'}
  (a₁ : F₁ ⊣ U₁) (a₂ : F₂ ⊣ U₂) (b₁ : G₁ ⊣ V₁) (b₂ : G₂ ⊣ V₂)
end CategoryTheory.Adjunction

namespace CategoryTheory.Functor
variable {A : Type u₁} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A]
  [BraidedCategory A] [HasFunctorialFlatResolution A]
variable {B : Type u₂} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalClosed B]
  [BraidedCategory B] [HasFunctorialFlatResolution B]
variable {B' : Type u₃} [Category.{u + 1} B'] [Abelian B']
  [IsGrothendieckAbelian.{u + 1} B']
  [MonoidalCategory B'] [MonoidalPreadditive B'] [MonoidalClosed B']
  [BraidedCategory B'] [HasFunctorialFlatResolution B']
variable {C : Type u₄} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
variable (F₁ : A ⥤ B) (F₂ : B ⥤ C) (G₁ : A ⥤ B') (G₂ : B' ⥤ C)
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
end CategoryTheory.Functor

namespace CategoryTheory.Functor
variable {A : Type u₁} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A]
  [BraidedCategory A] [HasFunctorialFlatResolution A]
variable {B : Type u₂} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B]
  [MonoidalCategory B] [MonoidalPreadditive B] [MonoidalClosed B]
  [BraidedCategory B] [HasFunctorialFlatResolution B]
variable {B' : Type u₃} [Category.{u + 1} B'] [Abelian B']
  [IsGrothendieckAbelian.{u + 1} B']
  [MonoidalCategory B'] [MonoidalPreadditive B'] [MonoidalClosed B']
  [BraidedCategory B'] [HasFunctorialFlatResolution B']
variable {C : Type u₄} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
variable (F₁ : A ⥤ B) (F₂ : B ⥤ C) (G₁ : A ⥤ B') (G₂ : B' ⥤ C)
  [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {U₁ : B ⥤ A} {U₂ : C ⥤ B} {V₁ : B' ⥤ A} {V₂ : C ⥤ B'}
  [U₁.Additive] [U₂.Additive] [V₁.Additive] [V₂.Additive]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits V₁] [PreservesFiniteColimits V₁]
  [U₂.PreservesKInjectiveComplexes] [V₂.PreservesKInjectiveComplexes]
  (a₁ : F₁ ⊣ U₁) (a₂ : F₂ ⊣ U₂) (b₁ : G₁ ⊣ V₁) (b₂ : G₂ ⊣ V₂)
end CategoryTheory.Functor

-- Preserve the concrete geometric functors while checking the abstract identities.
attribute [local irreducible] AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

-- Do not expand the canonical comparisons during tactic matching.
attribute [local irreducible]
  AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarPathIso

end AlgebraicGeometry.ProEtale.CondensedRing
