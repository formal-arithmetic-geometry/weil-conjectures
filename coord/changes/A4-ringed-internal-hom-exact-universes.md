# CategoryTheory.RingedHomUniverses.ringedInternalHom_exact

## Reason

The small etale site has object universe `u + 1` and morphism universe `u`. The
existing equal-universe theorem cannot express the target application. The returned
repair specifically forbids changing `RingedInternalHomExactRestriction` and asks for
an independent-universe exactness interface while preserving published consumers.

## Old

No independent-universe two-clause theorem was available to the target module; the
recorded shift module exports the normalized shift and covariant exactness pieces.

## New

A4 adds the new module `Sheaf.Algebra.Homology.RingedInternalHomExactUniverses`
with `CategoryTheory.RingedHomUniverses.ringedInternalHom_exact`. Its two conjuncts
state the contravariant first-variable and covariant second-variable clauses for
`derivedInternalHomOfUniverses` at independent universes. The proof remains the
named exactness hole from the existing node.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SfHomTriangulated | A4 | Publicly imports the new interface and specializes it at `(u+1,u,u+1,w)`. |
| Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses | S6 | Unchanged; its normalized shift and covariant exactness declarations are reused. |
| Sheaf.Algebra.Homology.RingedInternalHomExactRestriction | unclaimed | Unchanged; original small-site theorem and signature remain intact. |

## Status

landed 20261020T230706-L-601064 2026-10-20 (merge of deliver/A4/Sheaf.Paper.SfHomTriangulated)
