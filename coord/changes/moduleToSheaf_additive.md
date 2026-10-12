# AlgebraicGeometry.moduleToSheaf_additive

## Reason

The proof requires an `Additive` instance for `SheafOfModules.toSheaf`. The declaration is private and fully proved. The static checker conservatively
classifies added instances and the file-local `open scoped ZeroObject` command as
interface changes. This record documents both additions for independent review.
No existing definition or statement is modified.

## Old

No declaration in `Sheaf.AlgebraicGeometry.SupportedQCohTriangulated`.

## New

```lean
private instance moduleToSheaf_additive (X : Scheme.{u}) :
    (SheafOfModules.toSheaf.{u} (moduleRings X.toRingedSpace)).Additive where
  map_add := by intros; rfl
```

The file also adds `open scoped ZeroObject` for the notation in the zero-object proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SupportedQCohTriangulated | J2 | Uses the instance in the zero and stalk exactness proofs. |

## Status

landed 20261012T152347-L-2313130 2026-10-12 (merge of deliver/J2/Sheaf.AlgebraicGeometry.SupportedQCohTriangulated)
