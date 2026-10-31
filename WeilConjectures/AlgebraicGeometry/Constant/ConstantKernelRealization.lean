/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ProEtaleCoefficients.SingleConeKernel
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantKernelFiniteTypeReduction
public import WeilConjectures.ProEtaleCoefficients.BoundedConstructibleCounterexample.NonFiniteMultiplicationKernel
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! # Constant realization of the square-zero multiplication map

This records the coefficient-ring and module construction needed by the cone
counterexample.  Source: the construction paragraph of
`det-def-sfb-bounded-constructible.proof.md` (blueprint: lem-sfb-constant-kernel-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- A separably closed affine point and a constant commutative ring object carrying the
square-zero coefficient ring admit modules and a multiplication morphism whose kernel is
the constant square-zero ideal.  The endpoint modules are regular and zero, hence have
bounded constructible degree-zero realizations.  Constructing the comparison isomorphism
requires the sectionwise constant-module equivalence and the commutative-site realization.
(blueprint: lem-sfb-constant-kernel-realization) -/
theorem exists_constant_kernel_realization :
    ∃ (X : Scheme.{u})
      (R : CommMon (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}))
      (M N : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R.X)
      (f : M ⟶ N),
      boundedConstructible R.X ((DerivedCategory.singleFunctor _ 0).obj M) ∧
      boundedConstructible R.X ((DerivedCategory.singleFunctor _ 0).obj N) ∧
      (∀ hK : IsConstructibleModuleObject R.X (kernel f), False) := by
  sorry

end AlgebraicGeometry.ProEtale
