# Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyColimit imports

## Reason

The colimit theorem does not use PerfectComplex in its signature, and its proof uses
the principal-unit theorem and the structural core theorem through plain imports.
Prune the unused public import instead of exporting proof support. The first dry run
correctly required a change record because removing a public import changes exports.
No declaration signature, definition, or target meaning changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.KoszulOpenSystem
public import Sheaf.AlgebraicGeometry.PerfectComplex
```

## New

```lean
public import Sheaf.AlgebraicGeometry.KoszulOpenSystem
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomology | unclaimed in local snapshot | Its own public import of Sheaf.AlgebraicGeometry.PerfectComplex retains every previously available perfect-complex declaration and instance. Its signatures and proof need no adaptation; compile the original against the sandbox overlay. |

`tools/downstream.py Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyColimit
--direct` lists only the module above. The transitive command lists 352 modules. All
transitive import paths from the changed module go through that sole direct importer,
which still publicly imports PerfectComplex. Consequently the export change does not
propagate to any of the 352 downstream modules. No target definition or statement is
changed, and no second target-statement review is reopened.

## Status

landed 20261013T040748-L-3948812 2026-10-13 (merge of deliver/J2/Sheaf.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyColimit)
