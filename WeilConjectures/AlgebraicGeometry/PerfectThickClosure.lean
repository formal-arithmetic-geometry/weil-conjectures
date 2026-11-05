/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.AlgebraicGeometry.PerfectSummand
import all WeilConjectures.AlgebraicGeometry.PerfectTwoOutOfThree
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-! # Perfect complexes form a thick subcategory

Source: literature/stacks-project/cohomology.tex, Tags 08CR (lemma-two-out-of-three-perfect)
and 08CS (lemma-summands-perfect), and Definition 08CM (blueprint: lem-pc-perfect-thick-closure).
-/

@[expose] public section

universe u w v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
