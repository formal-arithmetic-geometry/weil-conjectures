/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

import WeilConjectures.Algebra.Homology.BifunctorSingleNaturality
import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
public import WeilConjectures.Algebra.Homology.InternalKFlatScalarTowerRealization

/-! # Realizing a scalar tower on native K-flat internal modules

This is the internal-module counterpart of the scalar realization in
`lem-pe-kflat-scalar-tower-realization`. It concerns individual scalar extensions,
their transitions and units; it involves neither products nor inverse limits.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod.KFlatScalarTower

section Computation
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

variable {T : C} [MonObj T] [IsCommMonObj T]
  (ψ : S ⟶ T) [IsMonHom ψ] (χ : R ⟶ T) [IsMonHom χ]
  (h : φ ≫ ψ = χ)

end Computation

attribute [local irreducible] extendTensorIso extendTensorNatIso extendTensorRightNatIso

section TensorTransport
variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C]

end TensorTransport

section StepNaturality

end StepNaturality

section RepresentativeTransport

end RepresentativeTransport

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  (R : C) [MonObj R] [IsCommMonObj R]
  (S : ℕ → C) [∀ n, MonObj (S n)] [∀ n, IsCommMonObj (S n)]
  (q : ∀ n, R ⟶ S n) [∀ n, IsMonHom (q n)]
  (r : ∀ n, S (n + 1) ⟶ S n) [∀ n, IsMonHom (r n)]
  (h : ∀ n, q (n + 1) ≫ r n = q n)

variable (B : ℕ → Mod C R) (ι : ∀ n, 𝟙_ (Mod C R) ⟶ B n)
  (τ : ∀ n, B (n + 1) ⟶ B n)

section
set_option backward.defeqAttrib.useBackward true

namespace PrincipalTensorAux

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [IsGrothendieckAbelian.{v} A] [Abelian.HasFunctorialFlatResolution A]

end PrincipalTensorAux

end

end CategoryTheory.Mod.KFlatScalarTower
