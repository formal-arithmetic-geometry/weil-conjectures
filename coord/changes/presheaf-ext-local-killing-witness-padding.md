# CategoryTheory.Sheaf.exists_presheaf_ext_local_killing_witness

## Reason

Upstream review #1428 requests removing the padded conclusion `∃ h : vanishing, True`.
The conclusion now states the vanishing equation directly. The old and new propositions
are logically equivalent: extract h in one direction, and pair a vanishing proof with
True.intro in the other. No hypotheses, presheaf universes or Ext degrees change.

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
      ∃ h : (Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
        (Functor.whiskerRight f AddCommGrpCat.free))).comp x (Nat.zero_add q) = 0, True
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
| Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling | T3 | The sole caller exists_presheaf_ext_local_killing applies the corrected theorem directly; its signature is unchanged. |

`tools/downstream.py --uses exists_presheaf_ext_local_killing_witness` lists only this
module as a user. A repository-wide name search confirms no external callers.
The 1690 transitive importing modules use an unchanged public local-killing theorem;
none refers to the witness declaration. No adaptations outside the held item are needed.
No target statement or definition changes, so no target meaning review is reopened.

## Status

landed 20261013T190156-L-3221515 2026-10-13 (merge of deliver/T3/Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling)
