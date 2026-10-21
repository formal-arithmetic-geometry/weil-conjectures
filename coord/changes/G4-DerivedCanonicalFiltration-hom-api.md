# DerivedCanonicalFiltration filtered morphism API restoration

## Reason

Restore the quarantined module after the official upstream filtration API retired the duplicate
`FilteredObject.HomPreservingSteps` structure. The complete proof archive uses that retired name;
the current API is `FilteredObject.Hom` with the same fields and preservation condition.

## Old

```lean
FilteredObject.HomPreservingSteps A B
```

## New

```lean
FilteredObject.Hom A B
```

All occurrences in private helpers and the existing theorem signature were migrated. The theorem
meaning, proof, imports, and public declaration name are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.DerivedCanonicalFiltration | G4 | restored module and current API references |
| Sheaf.Algebra.Homology.CanonicalTruncationFiltration | V1 | uses the same official `FilteredObject.Hom` API; unaffected |
| Sheaf.Algebra.Homology.FilteredTensorLocalization | unclaimed; quarantine | uses the same official API; unaffected |

## Status

landed 20261021T012400-L-2183416 2026-10-21 (merge of deliver/G4/Sheaf.Algebra.Homology.DerivedCanonicalFiltration)
