/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Mates of squares commuting with shifts

If the adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` are compatible with shifts and a square
`α : G ⋙ L₂ ⟶ L₁ ⋙ H` commutes with the shifts, then so does its mate
`R₁ ⋙ G ⟶ H ⋙ R₂`: the mate is a composite of whiskered units, counits, `α` and unitors and
associators, all of which commute with the shifts.
-/

@[expose] public section

namespace CategoryTheory


variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A] [HasShift E A] [HasShift F A]
  {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  [G.CommShift A] [H.CommShift A] [L₁.CommShift A] [R₁.CommShift A] [L₂.CommShift A]
  [R₂.CommShift A] (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.CommShift A] [adj₂.CommShift A]

/-- The mate of a square of functors commuting with shifts commutes with shifts: for the square
`α` on the left, its mate on the right commutes with the shifts.

```
    C ──L₁──▶ D             C ◀──R₁── D
    │         │             │         │
  G │    α    │ H         G │  mate   │ H
    ▼         ▼             ▼         ▼
    E ──L₂──▶ F             E ◀──R₂── F
```
-/
instance NatTrans.CommShift.mateEquiv (α : TwoSquare G L₁ L₂ H)
    [NatTrans.CommShift α.natTrans A] :
    NatTrans.CommShift (mateEquiv adj₁ adj₂ α).natTrans A := by
  have h : (_root_.CategoryTheory.mateEquiv adj₁ adj₂ α).natTrans =
      (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (R₁ ⋙ G) adj₂.unit ≫
        (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft _ (Functor.associator _ _ _).inv ≫
        Functor.whiskerLeft R₁ (Functor.whiskerRight α.natTrans R₂) ≫
        Functor.whiskerLeft _ (Functor.associator _ _ _).hom ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight adj₁.counit (H ⋙ R₂) ≫ (Functor.leftUnitor _).hom := rfl
  rw [h]
  infer_instance

end CategoryTheory
