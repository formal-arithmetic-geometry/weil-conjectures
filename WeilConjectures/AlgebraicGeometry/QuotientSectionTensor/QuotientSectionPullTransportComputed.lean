/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionPullTransportScalarComputation
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionPullTransportGeometricComputation

/-! # Pullback compatibility on scalar-computed representatives

Source: Stacks Project, Tags 06YY, 0D6D and 07A6.
(blueprint: lem-sfb-quotient-section-pull-transport-computed)
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Share the large inferred cochain structures while checking the diagram proof.
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient

attribute [local semireducible] QuotientChange.L
attribute [local implicit_reducible] QuotientChange.L
  InternalAbelianSheafModule.sectionRingSheaf
  DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh HomotopyCategory.quotient
  CategoryTheory.Functor.mapHomologicalComplex CategoryTheory.Functor.mapHomotopyCategory
  CategoryTheory.catToReflQuiver
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafSymmetricCategory

-- Extract a normalization field without repeating its large remaining conjunction.
-- Give lifted comparisons iterated functor types at their construction boundary.

-- Reindex normalization while all four ordinary functors remain abstract.

-- Pasting is checked over abstract categories before any sheaf functor is inserted.
section
variable {C0 : Type*} [Category* C0]
variable {C1 : Type*} [Category* C1]
variable {C2 : Type*} [Category* C2]
variable {C3 : Type*} [Category* C3]
variable {S0 : Type*} [Category* S0]
variable {S1 : Type*} [Category* S1]
variable {S2 : Type*} [Category* S2]
variable {S3 : Type*} [Category* S3]
variable {D0 : Type*} [Category* D0]
variable {D1 : Type*} [Category* D1]
variable {D2 : Type*} [Category* D2]
variable {D3 : Type*} [Category* D3]
variable {E0 : Type*} [Category* E0]
variable {E1 : Type*} [Category* E1]
variable {E2 : Type*} [Category* E2]
variable {E3 : Type*} [Category* E3]

end

-- Share the specified abelian and localization structures without changing category types.
universe ua va wa ub vb wb

@[reducible] private def structure_pair
    {A : Type ua} {B : Type ub} [Category.{va} A] [Category.{vb} B]
    [abA : Abelian A] [abB : Abelian B]
    [derA : HasDerivedCategory.{wa} A] [derB : HasDerivedCategory.{wb} B]
    (_F : DerivedCategory A ⥤ DerivedCategory B) :
    DerivedStructures.{ua, va, wa} A × DerivedStructures.{ub, vb, wb} B :=
  ⟨⟨abA, derA⟩, ⟨abB, derB⟩⟩

-- Lift ordinary comparisons inside the generic cochain diagram constructor.
section
variable {A0 : Type*} [Category* A0] [abA0 : Abelian A0]
  [derA0 : HasDerivedCategory A0]
variable {A1 : Type*} [Category* A1] [abA1 : Abelian A1]
  [derA1 : HasDerivedCategory A1]
variable {A2 : Type*} [Category* A2] [abA2 : Abelian A2]
  [derA2 : HasDerivedCategory A2]
variable {A3 : Type*} [Category* A3] [abA3 : Abelian A3]
  [derA3 : HasDerivedCategory A3]
variable {B0 : Type*} [Category* B0] [abB0 : Abelian B0]
  [derB0 : HasDerivedCategory B0]
variable {B1 : Type*} [Category* B1] [abB1 : Abelian B1]
  [derB1 : HasDerivedCategory B1]
variable {B2 : Type*} [Category* B2] [abB2 : Abelian B2]
  [derB2 : HasDerivedCategory B2]
variable {B3 : Type*} [Category* B3] [abB3 : Abelian B3]
  [derB3 : HasDerivedCategory B3]
variable (G₀ : A0 ⥤ A1) [G₀.Additive]
variable (H₀ : A2 ⥤ A3) [H₀.Additive]
variable (S₀ : A0 ⥤ A2) [S₀.Additive]
variable (T₀ : A1 ⥤ A3) [T₀.Additive]
variable (g₀ : B0 ⥤ B1) [g₀.Additive]
variable (h₀ : B2 ⥤ B3) [h₀.Additive]
variable (s₀ : B0 ⥤ B2) [s₀.Additive]
variable (t₀ : B1 ⥤ B3) [t₀.Additive]
variable (e₀ : A0 ⥤ B0) [e₀.Additive]
variable (e₁ : A1 ⥤ B1) [e₁.Additive]
variable (e₂ : A2 ⥤ B2) [e₂.Additive]
variable (e₃ : A3 ⥤ B3) [e₃.Additive]

end

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']

variable
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

-- Use the fixed derived-equivalence functor in the localization interface itself.

attribute [local irreducible] complex_iso complex_comp_iso section_localization_iso

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
