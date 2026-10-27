# AlgebraicGeometry.ProEtale.AmbientClopenRestriction.transition

## Reason

Make the underlying linear-map application explicit, avoiding repeated coercion search
through the evaluated module's transported scalar structure. This is an eta expansion of
the original function: module morphism coercion applies its `.hom` linear map. The actual
adjacent semilinear transition, its signature and all coefficient categories are unchanged.
Targets using this definition should be reread with this definitional refactoring.

## Old

```lean
def transition (m : Option ℕ) (X : Scheme.{u})
    (M : Modules l E m X) (n : ℕ) (T : X.ProEt) :
    ((sections l E m X (n + 1)).obj M).obj (op T) →
      ((sections l E m X n).obj M).obj (op T) :=
  match m with
  | some _ => id
  | none => M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 T)).op
```

## New

```lean
def transition (m : Option ℕ) (X : Scheme.{u})
    (M : Modules l E m X) (n : ℕ) (T : X.ProEt) :
    ((sections l E m X (n + 1)).obj M).obj (op T) →
      ((sections l E m X n).obj M).obj (op T) :=
  match m with
  | some _ => id
  | none => fun x ↦ (M.val.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 T)).op).hom x
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness | R2 | identical transition function |

`tools/downstream.py ... --uses transition` reports only this item and zero downstream
modules in the current source. No forced adaptations.

## Status

landed 20261025T181016-L-4062981 2026-10-25 (merge of deliver/R2/Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness)
