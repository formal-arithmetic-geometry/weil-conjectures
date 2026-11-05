/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceLineLocalization
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# AffineTraceLinePurity
Source: blueprint sk-prop-an, Steps 5(b) and 6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Preadditive
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
