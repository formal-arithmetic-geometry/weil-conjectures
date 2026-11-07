/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeHypotheses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorTotal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientTensorLocalization

set_option linter.privateModule false

/-! # The localized scalar total tensor path

This normalizes the scalar path using the ordinary signed total tensor square.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-total-path)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 2048
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategoryStruct
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Mod.extendScalars Mod.comap internalScalarExtension
  ModuleRingedComparison.tensor ModuleRingedComparison.tensorComparison
  ModuleRingedComparison.qTensor
  ModuleRingedComparison.totalComparison ModuleRingedComparison.ordinaryTensorComparison
  Localization.Monoidal.tensorBifunctor

-- Match native prolongations before reducing concrete section constructions.
attribute [local irreducible] HomologicalComplex₂.total Mod.inducingFunctorData
  InternalAbelianSheafModule.sectionModuleEquivalence SheafOfModules.monoidalCategory

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]

private theorem paste_total_path {𝒞 : Type*} [Category 𝒞]
    {A B C D E F G H I J J₀ K L M N P : 𝒞}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D} {d : D ⟶ E}
    {e : E ⟶ F} {f : F ⟶ G} {g : A ⟶ H} {h : H ⟶ I}
    {i : B ⟶ I} {j : I ⟶ J} {k : J ⟶ E} {l : J ⟶ J₀}
    {m₀ : J₀ ⟶ F} {m : H ⟶ K} {n : K ⟶ L} {o : L ⟶ J₀}
    {p : L ⟶ M} {q : M ⟶ N} {r : N ⟶ G} {s : K ⟶ P} {t : P ⟶ M}
    (hfac : b ≫ c ≫ d = i ≫ j ≫ k) (hnat : k ≫ e = l ≫ m₀)
    (hp : g ≫ h = a ≫ i) (hscalar : m ≫ n ≫ o = h ≫ j ≫ l)
    (htotal : p ≫ q ≫ r = o ≫ m₀ ≫ f) (hlocal : s ≫ t = n ≫ p) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f = g ≫ m ≫ s ≫ t ≫ q ≫ r := by
  rw [reassoc_of% hfac, reassoc_of% hnat, ← reassoc_of% hp,
    ← reassoc_of% hscalar, ← htotal, ← reassoc_of% hlocal]

attribute [local irreducible] coefficientInternalScalarComplex
  coefficientSectionScalarTotal SheafOfModules.scalarPairComplexComparison
  internalScalarTensorComparison


end AlgebraicGeometry.ProEtale.CondensedRing
