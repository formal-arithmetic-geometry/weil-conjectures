/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ZigzagModule
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.Algebra.Homology.ZigzagZeroComponentBoundary
import WeilConjectures.Algebra.Homology.ZigzagBoundaryReduction

/-! # Exact-row zig-zags are trivial

Source: Stacks Project, Algebra, Lemma Tag 00M1, injectivity argument
(blueprint: lem-weil-pbc-double-complex-zigzag-trivial-if-row-boundary).
-/

@[expose] public section

open CategoryTheory

namespace HomologicalComplex₂

universe u v

variable {R : Type u} [CommRing R]

end HomologicalComplex₂
