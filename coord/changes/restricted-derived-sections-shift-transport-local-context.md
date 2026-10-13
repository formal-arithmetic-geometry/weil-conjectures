# restrictedDerivedSections_shiftTransport

## Reason

The proof uses the existing abelian-category K-injective APIs and the existing cached
etale and sheafification instances. The static checker flags the additional `open` and
`attribute [local instance]` commands as a possible interface change, even though they
only affect elaboration within this file. This record documents those commands.
No definition, theorem signature, visibility, target, or exported instance changes.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
```

There was no local-instance attribute command in this module.

## New

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

attribute [local instance] etaleComposition etaleIdentities etalePullbacks
  etaleBaseChange sheafifyInstance weakSheafifyInstance
```

All six declarations already exist in the publicly imported module
`Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap`.
The attributes are local; the new abelian-category names are used only in proved private
helpers. The proof imports remain non-public. Existing signatures are identical.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RestrictedDerivedSectionShiftComparison | unclaimed | No interface change; the same theorem is now proved. No adaptation. |

This is the direct importer of the item. The local attributes and open namespaces do not
propagate to importers, so no downstream module needs adaptation and no target statement
or definition meaning changes.

## Status

landed 20261013T095931-L-2451897 2026-10-13 (merge of deliver/B3/Sheaf.AlgebraicGeometry.RestrictedDerivedSectionsShiftTransport)
