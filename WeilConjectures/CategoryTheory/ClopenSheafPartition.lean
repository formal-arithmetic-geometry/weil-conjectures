/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Subterminal

/-!
# Finite clopen partitions of a site

Source: the finite disjoint open-and-closed decomposition used in the proof of
the Weil mixedness theorem (blueprint: def-zl-clopen-sheaf-partition).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A finite family of pairwise disjoint subterminal sheaves which covers every site object.

The subterminal sheaves are the open-and-closed pieces.  The `cover` field says that every
object is covered by arrows carrying a section of one of the pieces.  Pairwise disjointness
says that a simultaneous section of distinct pieces forces the empty sieve to cover.
This allows the singleton section sets that every sheaf has on an empty-covered object.

Source: Stacks Project, Tags 0791 and 00WK; (blueprint: def-zl-clopen-sheaf-partition).
-/
structure ClopenSheafPartition {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (I : Type w) where
  pieces : I → Sheaf J (Type u)
  finite : Finite I
  subterminal : ∀ i, IsSubterminal (pieces i)
  disjoint : ∀ (i j : I), i ≠ j →
    ∀ (V : C), Nonempty ((pieces i).obj.obj (op V)) →
      Nonempty ((pieces j).obj.obj (op V)) → (⊥ : Sieve V) ∈ J V
  cover : ∀ (V : C), ∃ S : Presieve V, Sieve.generate S ∈ J V ∧
    ∀ (W : C) (f : W ⟶ V), S f → ∃ i : I, Nonempty ((pieces i).obj.obj (op W))

end CategoryTheory
end
