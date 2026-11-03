/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Data.Finite.Sigma

/-! # Splitness of a normalized simplicial attachment

Source: Stacks Project, Tag 0DAU, characterization by invertible degeneracy components,
and Tag 0DAV, the new index set.
(blueprint: lem-weil-pbc-site-split-attachment-split).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FormalSplitAttachment

variable {D : Type u} [Category.{v} D] {n : ℕ}

private abbrev restriction (L : SimplicialObject.Truncated (FormalCoproduct.{w} D) (n + 1)) :=
  (SimplicialObject.Truncated.trunc (FormalCoproduct.{w} D) (n + 1) n).obj L

end CategoryTheory.FormalSplitAttachment
