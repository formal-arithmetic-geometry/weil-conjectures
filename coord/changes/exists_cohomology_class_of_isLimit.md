# AlgebraicGeometry.Etale.exists_cohomology_class_of_isLimit

## Reason

The landed proof does not use the torsion hypothesis. Rename the binder to `_hF` and
remove the redundant `have _ := hF` line to make that fact explicit and silence Lean's
unused-variable warning. The theorem type and all hypotheses are definitionally unchanged;
only the source-level binder name changes.

## Old

```lean
(hF : F.IsTorsion) (q : ℕ) :
```

## New

```lean
(_hF : F.IsTorsion) (q : ℕ) :
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity | unclaimed | binder name is irrelevant; no source change required |

## Status

landed 20261015T225534-L-3017350 2026-10-15 (merge of deliver/D4/Sheaf.AlgebraicGeometry.EtaleCohomologyClassDescent)
