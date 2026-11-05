/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonInheritanceFixedDegree

/-! # Tensor inheritance for localized cohomology comparisons

Source: Stacks Project, perfect.tex, Tag 0DJA(1), local computation using Tag 0BYJ.
(blueprint: lem-pc-localized-tensor-comparison-inheritance).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ModuleCat

end ModuleCat
