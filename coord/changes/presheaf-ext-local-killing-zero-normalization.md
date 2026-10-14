# CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness

## Reason

Upstream review #1428 requested a direct vanishing equation. The padding repair
has already landed. Normalize that equation to the same unannotated `= 0` form
as its sole caller. Lean infers the Ext type from the left side; the elaborated
statement, hypotheses, universes, and target meanings are identical.

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
        (Functor.whiskerRight f AddCommGrpCat.free))).comp x (Nat.zero_add q)
        = (0 : Ext
          ((presheafToSheaf J AddCommGrpCat).obj (E ⋙ AddCommGrpCat.free)) F q)
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
        (Functor.whiskerRight f AddCommGrpCat.free))).comp x (Nat.zero_add q) = 0
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling | C4 | Sole caller applies the witness unchanged. |

The downstream-use check and source search find no other caller of this
witness. No adapted modules or changed definitions; no target review reopens.

## Status

landed 20261014T045608-L-1572056 2026-10-14 (merge of deliver/C4/Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling)
