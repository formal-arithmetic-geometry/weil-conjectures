/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Termwise products of K-injective complexes

Source: Stacks Project, Tag 0BK6, and upstream review #1428.
(blueprint: lem-pc-ringed-space-product-kinjective).

The duplicate `CochainComplex.termwise_product_isKInjective_and_isLimit` is retired.
Its callers use the existing homotopy product and K-injective Hom comparison APIs.
This compatibility module declares no new theorem and has no remaining imports.
-/

@[expose] public section
