# ModuleSheafificationAffineRestriction

## Reason

The proof changes the module-level `open` command and uses the categorical dense-subsite
lemmas to make the proof compile. This is an interface-visible command change, so it
is recorded as required by stage 3.

## Old

`open CategoryTheory`

## New

`open CategoryTheory CategoryTheory.Functor Opposite`

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ModuleSheafificationAffineRestriction | U3 | proof elaboration only |
| Sheaf.AlgebraicGeometry.QCohAcyclicDerivedPushforwardCohomology | unclaimed | Direct importer and theorem user; compiles against delivery; signature and meaning unchanged; no adaptation required |

## Status

landed 20261012T135325-L-1696484 2026-10-12 (merge of deliver/U3/Sheaf.AlgebraicGeometry.ModuleSheafificationAffineRestriction)
