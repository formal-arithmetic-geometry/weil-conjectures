/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantProjectionMaps
import WeilConjectures.AlgebraicGeometry.CompletedConstantPresentation.CompletedConstantCompletionRightExact
import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantRankOneComparison
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Invertibility of the canonical finite-module comparison

Source: Stacks Project, More on Algebra, Tag 0912, and Modules on Sites, Tags 093J--093M.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
