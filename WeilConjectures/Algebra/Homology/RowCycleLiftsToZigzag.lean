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
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Row-cycle lifts to a zig-zag

Source: Stacks Project, Algebra, Lemma Tag 00M1, proof lines 18464--18481
(blueprint: lem-weil-pbc-double-complex-row-cycle-lifts-to-zigzag).
-/

@[expose] public section

open CategoryTheory DirectSum

namespace HomologicalComplex₂

variable {R : Type*} [CommRing R]

end HomologicalComplex₂
