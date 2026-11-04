/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products

public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor

/-!
# Relative profinite test schemes

Source: RefactorInstruction, Section 4, equations finite-XI and XS, Lemma lem:XS;
ModuleObject/Basic.lean, module docstring, lines 38–52; Stacks Project, Tag 097D
(blueprint: lem-weil-pbc-profinite-test-object-functor).
-/
