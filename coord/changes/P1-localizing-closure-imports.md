# AlgebraicGeometry.ProEtale.localizingClosure_exists

## Reason

The existence theorem is uniform in the generating class and does not use the Tor-amplitude
well-definedness assertions. Remove their unused public import to prune this dependency.
The theorem signature and the definitions of localizing subcategory and closure are unchanged.

## Old

```lean
public import Sheaf.Paper.ConstantModelTorAmplitude
```

## New

The import is removed. All remaining public imports are retained verbatim.
Proof-only dependencies are private imports; the two added helpers are private.

## Users

All six direct importers were checked as individual files against the changed module.
No consumer adaptation or claim is needed. None uses a declaration unique to the removed
module without another import. All eleven transitive downstream modules are listed below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AmbientIndDerivedSums | F5 | Direct importer; unchanged statement and proof; compile checked. |
| Sheaf.Paper.BrownHypothesesGeneration | E1 | Direct importer; unchanged statement and proof; compile checked. |
| Sheaf.Paper.ConstructibleCompactness | U7 | Direct importer; unchanged statement and proof; compile checked. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | Direct importer; unchanged statement and proof; compile checked. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Direct importer; unchanged statement and proof; compile checked. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | H9 | Direct importer; unchanged statement and proof; compile checked. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6 | Indirect importer; no exported declaration or type changes. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7 | Indirect importer; no exported declaration or type changes. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | N4 | Indirect importer; no exported declaration or type changes. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | U3 | Indirect importer; no exported declaration or type changes. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | G9 | Indirect importer; no exported declaration or type changes. |

The assigned module itself retains its complete original theorem signature.
No target statement or definition changes, so no mathematical target review is reopened.

## Status

landed 20261018T145108-L-3642742 2026-10-18 (merge of deliver/P1/Sheaf.Paper.LocalizingClosureExistence)
