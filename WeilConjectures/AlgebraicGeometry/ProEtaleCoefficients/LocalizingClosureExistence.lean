/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.GrothendieckDerivedCoproductsColimit

import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
/-!
# Existence and thickness of the localizing closure

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-localizing-closure,
node det-def-localizing-closure-existence, clauses (1)--(3)
(blueprint: det-def-localizing-closure-existence).

Coefficients are arbitrary condensed rings, including noncommutative rings. The
module category is Mathlib's category of internal left modules over the actual
pulled-back ring object. Index sets live in `Type (u + 1)`; the larger universe
of the type of all module objects does not enlarge the required coproduct existence.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale

open Opposite CategoryTheory.Pretriangulated.Opposite

end AlgebraicGeometry.ProEtale
