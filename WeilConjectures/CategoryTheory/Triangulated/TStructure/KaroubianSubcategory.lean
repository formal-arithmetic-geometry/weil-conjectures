/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Karoubian
public import WeilConjectures.Mathlib.CategoryTheory.Idempotents.FullSubcategory

/-!
# Idempotent completeness of subcategories of bounded objects

Let `C` be a triangulated category with a t-structure `t`. Every idempotent of a `t`-bounded
object of `C` splits (`CategoryTheory.Triangulated.TStructure.isSplit_of_bounded`). Hence a full
subcategory of `C` consisting of `t`-bounded objects and closed under retracts is idempotent
complete, and its inclusion into its Karoubi envelope is an equivalence.
-/

@[expose] public section

namespace CategoryTheory.Triangulated.TStructure

open Idempotents

variable {C : Type*} [Category* C] [Preadditive C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (t : TStructure C)

/-- An idempotent of a `t`-bounded object splits. -/
lemma isSplit_of_bounded {X : C} (hX : t.bounded X) {p : X ⟶ X} (hp : p ≫ p = p) :
    IsSplit p := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hX
  have : t.IsLE X (a + ((b - a).toNat : ℕ)) := t.isLE_of_le X b _ (by lia)
  exact t.isSplit_of_isGE_of_isLE (b - a).toNat X a p hp

/-- A full subcategory of `t`-bounded objects which is closed under retracts is idempotent
complete. -/
lemma isIdempotentComplete_fullSubcategory_of_le_bounded (P : ObjectProperty C)
    [P.IsStableUnderRetracts] (hP : P ≤ t.bounded) : IsIdempotentComplete P.FullSubcategory :=
  isIdempotentComplete_fullSubcategory P fun _ _ hX hp ↦ t.isSplit_of_bounded (hP _ hX) hp

end CategoryTheory.Triangulated.TStructure
