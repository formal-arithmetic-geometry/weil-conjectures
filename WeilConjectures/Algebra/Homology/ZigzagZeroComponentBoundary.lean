/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ZigzagModule
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.Algebra.Homology.ZigzagModuleFunctorial
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # Exact-row induction for a zero-component zig-zag

Source: Stacks Project, Algebra, Tag 00M1 (`lemma-no-spectral-sequence`),
injectivity argument. (blueprint: new-zigzag-zero-component-boundary).
-/

@[expose] public section

open CategoryTheory
namespace HomologicalComplex₂
universe u v
variable {R : Type u} [CommRing R]

end HomologicalComplex₂
