/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure

/-! # The canonical localizing pullback preservation proposition

Source: blueprint latest, sec-six-functors-basics/sk-prop-proper-base-change-unbounded,
sk-prop-proper-base-change-unbounded-pullback.proof.md, exactness, sums and localizing closures
(blueprint: def-zl-unbounded-localizing-pullback).

These two declarations are moved from
`WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback` with their
names, signatures, and bodies unchanged. The canonical shift is constructed from the
existing exact-derived comparison; the proposition records the ambient and restricted
preservation clauses without asserting them. The localizing hull and constant-model
constructibility are the existing imported definitions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local instance] unboundedLocalizingPullbackCommShift

end AlgebraicGeometry.ProEtale
