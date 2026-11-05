/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Category.ModuleCat.Kernels
/-! # Finite reductions of integral scalar-model constructible sheaves

The coordinate definitions are shared by the chart comparison and descent.
(blueprint: def-sfb-finite-model-quotient-coordinates).

Source: blueprint main-20261015, localizing-closure ctf-equals-bc proof,
Local models, Locality and Strata paragraphs; Stacks Tags 093J, 093M, 06YQ, 06YY and 09AJ
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible).

The index n denotes the positive exponent n+1. All reductions use the existing actual
quotient map and take values in the derived category over the quotient coefficient ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteModelQuotient

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Named quotient-module coordinates for the specified category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
@[instance_reducible] def quotientModuleCategory (n : ℕ) (T : Scheme.{u}) :
    Category.{u + 1} (quotientModules l E n T) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  inferInstanceAs (Category (FiniteDiscreteOrdinary.Internal (R l E n) T))

/-- Named quotient-module coordinates for the specified category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
@[instance_reducible] def quotientModuleAbelian (n : ℕ) (T : Scheme.{u}) :
    @Abelian (quotientModules l E n T) (quotientModuleCategory l E n T) := by
  dsimp only [quotientModuleCategory, quotientModules]
  infer_instance

/-- Named quotient-module coordinates for the specified category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
@[instance_reducible] def quotientModuleDerived (n : ℕ) (T : Scheme.{u}) :
    @HasDerivedCategory.{u + 1} (quotientModules l E n T)
      (quotientModuleCategory l E n T) (quotientModuleAbelian l E n T) := by
  dsimp only [quotientModuleCategory, quotientModuleAbelian, quotientModules]
  infer_instance

attribute [instance] quotientModuleCategory quotientModuleAbelian quotientModuleDerived

/-- Exact quotient inverse image in the named module category.
Source: blueprint finite coefficient coordinates
(blueprint: def-sfb-finite-model-quotient-coordinates). -/
@[instance_reducible] def quotientUpperStar (n : ℕ) {V T : Scheme.{u}} (f : T ⟶ V) :
    quotientModules l E n V ⥤ quotientModules l E n T :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  CondensedRing.upperStar (FiniteDiscreteOrdinary.coefficient (R l E n)) f

end AlgebraicGeometry.ProEtale.FiniteModelQuotient
