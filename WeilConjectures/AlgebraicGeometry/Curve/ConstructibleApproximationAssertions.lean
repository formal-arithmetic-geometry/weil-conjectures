/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimit

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.AlgebraicGeometry.ConstructibleSubobjectPresentation
import WeilConjectures.AlgebraicGeometry.ConstantModuleSheavesForgetColimits
import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimitExtension
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import Mathlib.CategoryTheory.Presentable.Directed
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Constructible approximation for the eight assertions

Source: Stacks Project, Theorem 59.83.10 (03SC), first proof paragraph,
and Lemma 59.73.2 (03SA).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

open Etale

end AlgebraicGeometry
