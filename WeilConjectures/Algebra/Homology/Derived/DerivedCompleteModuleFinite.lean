/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.DerivedCompleteModuleComplex
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Torsion.Basic
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.RingTheory.FiniteModuleComplete
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Finiteness of derived-complete modules with finite residue

Source: Stacks Project, More on Algebra, Tag 09BA (`lemma-derived-complete-finite`),
specialized to an `I`-adically complete Noetherian ring
(blueprint: lem-weil-derived-complete-module-finite).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace ModuleCat

end ModuleCat
