/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.StrictDvrCoefficientSequence
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.SuccessiveQuotientFlatTensorSequence
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement

/-! # Flat tensor realization of the strict DVR coefficient sequence

Source: Stacks Project, Tag 0942, proof of lemma-bounded (1); Modules on Sites,
Tags 03EK and 03ER.
(blueprint: lem-sf-strict-dvr-flat-tensor-sequence)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u v r wR wS

open CategoryTheory CategoryTheory.Limits Opposite

open scoped ChangeOfRings

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})

open SheafOfModules

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  unrestrictedIntegralReductionExistence scalarReductionExistence
  unrestrictedIntegralTransition unrestrictedTowerTransition

end WeilConjectures
