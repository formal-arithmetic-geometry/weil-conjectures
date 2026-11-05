/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Whiskering

/-! # Descent of normalized derived comparisons

Source: Stacks 06YY and 0D6D; the complete generic proof from
IntegralComparisonSequenceSystems.
(blueprint: lem-sf-normalized-derived-comparison-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b c d e f
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace SequenceComparisonConstruction

universe g h wA wB wC wD

end SequenceComparisonConstruction
