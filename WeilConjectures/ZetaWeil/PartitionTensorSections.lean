/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import WeilConjectures.CategoryTheory.Sites.FiniteDisjointCover
import WeilConjectures.CategoryTheory.Sites.IsDisjointCover.DisjointSheafSections
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Tensor sections over finite disjoint partitions

Source: Stacks Project, Tags 03EK and 0F63.
(blueprint: lem-zl-partition-tensor-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})

section Partition
variable {W : C} {n : ℕ} {Y : Fin n → C} {f : ∀ i, Y i ⟶ W}
  (hf : J.IsDisjointCover f)

private def extend (M : Mods.{c, v, r} R) (i : Fin n) (x : M.val.obj (op (Y i))) :
    M.val.obj (op W) := by
  classical
  exact (GrothendieckTopology.IsDisjointCover.exists_type_map_eq hf (underlying.{c, v, r} R M)
    (Pi.single (M := fun j ↦ M.val.obj (op (Y j))) i x)).choose

include hf in
end Partition
end SheafOfModules
