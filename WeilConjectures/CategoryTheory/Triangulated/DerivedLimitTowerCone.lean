/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! # Limit of a tower of cochain complexes
Source: Mathlib, CategoryTheory.Limits.hasLimit_of_equalizer_and_product
(blueprint: lem-weil-derived-limit-tower-core-cone). -/

@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex

end CochainComplex
