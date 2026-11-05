/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Perfect ring complexes are closed under triangle extensions

Source: Stacks Project, More on Algebra, Tag 066R, lemma-two-out-of-three-perfect,
the first-and-third-imply-second case (blueprint: lem-sf-perfect-ring-triangle-closure).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Pretriangulated

namespace DerivedCategory

-- These helpers adapt the bounded-model proofs in
-- WeilConjectures.CategoryTheory.DerivedCategory.Perfect to an independent universe w.

end DerivedCategory
