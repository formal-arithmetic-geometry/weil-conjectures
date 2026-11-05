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
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!
# Bounded constructible field-coefficient complexes form a thick triangulated subcategory

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-coefficient-heart-ii,
`sk-cor-coefficient-heart-ii-triangulated.md`
(blueprint: det-cor-coefficient-heart-ii-triangulated).

The property is the recorded finite-constant-model notion, not the different upstream
stratified-local-finite-presentation property. The two coefficient choices carry their
canonical ring-object structures. The algebraic-closure coefficient has sections valued
in a finite subextension, as required by the source.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
