/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicOrdinaryScalarModel
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantCohomology
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Exact-functor factorizations for constant scalar models

Source: Stacks Project, Tags 05RU, 093J, 093M and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

attribute [local irreducible] completedAdicChangeData completedAdicScalar completedAdicRing
  Functor.mapDerivedCategory HasDerivedCategory.standard Functor.leftAdjoint

variable (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
  (V : X.Etale) (U : V.left.ProEt) (W : X.ProEt)
  (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ)

end AlgebraicGeometry.Scheme
