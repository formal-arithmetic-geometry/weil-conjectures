# CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness

## Reason

The padding requested by upstream review #1428 was removed in landing
20261013T190156-L-3221515. This delivery only makes the zero's Ext type
explicit. The old and new signatures elaborate to the same proposition;
no hypothesis, conclusion, definition or target meaning changes.

## Old

```lean
theorem exists_presheaf_ext_local_killing_witness
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (P : Cᵒᵖ ⥤ Type v)
    (q : ℕ) (hq : 0 < q)
    (x : Ext ((presheafToSheaf J AddCommGrpCat).obj (P ⋙ AddCommGrpCat.free)) F q) :
    ∃ (E : Cᵒᵖ ⥤ Type v) (f : E ⟶ P),
      Presheaf.IsLocallySurjective J f ∧
      (Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
        (Functor.whiskerRight f AddCommGrpCat.free))).comp x (Nat.zero_add q) = 0
```

## New

```lean
theorem exists_presheaf_ext_local_killing_witness
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (P : Cᵒᵖ ⥤ Type v)
    (q : ℕ) (hq : 0 < q)
    (x : Ext ((presheafToSheaf J AddCommGrpCat).obj (P ⋙ AddCommGrpCat.free)) F q) :
    ∃ (E : Cᵒᵖ ⥤ Type v) (f : E ⟶ P),
      Presheaf.IsLocallySurjective J f ∧
      (Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
        (Functor.whiskerRight f AddCommGrpCat.free))).comp x (Nat.zero_add q)
        = (0 : Ext
          ((presheafToSheaf J AddCommGrpCat).obj (E ⋙ AddCommGrpCat.free)) F q)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling | T3 | The sole caller applies the witness unchanged; its signature and proof remain identical. |

A source search for the witness name in both Lean roots finds only its
declaration and the caller above. No other module directly uses it.

## Status

landed 20261013T222416-L-1227531 2026-10-13 (merge of deliver/T3/Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling)
