/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Category.Grp.Ulift

/-! # Object cohomology equivalences normalized on cocycles

Source: Stacks Project, Section 01FT and Tag 06XR (1).
(blueprint: lem-weil-pbc-object-resolution-cocycle-equivalence)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

