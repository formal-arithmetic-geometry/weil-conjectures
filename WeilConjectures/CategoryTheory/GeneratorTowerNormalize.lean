/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Rotating, mapping and prepending zero to a generator tower

Source: Stacks Project, derived.tex, lemma-write-as-colimit (Tag 09SN), and
duality.tex, lemma-when-sheafy, proof of (3), Section Tag 0E4G.
(blueprint: lem-sc-generator-tower-normalize).
-/

@[expose] public section

universe u v c d

open CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace CategoryTheory

end CategoryTheory
