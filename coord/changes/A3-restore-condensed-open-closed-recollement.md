# Restoring condensed open/closed recollement

## Reason

The assigned coord/rework.tsv row preserves this module under quarantine after a cluster
restore was reverted. Its live Lean source is missing. Restore the actual proved theorem,
its private proof helpers, and its existing dependencies. This is a source restoration,
not a proof-hole closure or a change to the mathematical statement.

## Old

The live path lean/Sheaf/Paper/CondensedOpenClosedRecollement.lean is absent.
The authoritative 780-line source is preserved at
quarantine/Sheaf/Paper/CondensedOpenClosedRecollement.lean, with zero sorry proofs.
The DAG attachment still names the live path and
AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_closed_recollement.

## New

Restore the module byte for byte from that archive. The theorem signature, universes,
public imports, attributes, private helper names, and all proof bodies stay identical.
The theorem constructs the kernel exceptional adjoint and the two natural, shift-compatible
localization triangles, together with common-bound injective resolution models.
The original DAG attachment and proof dependencies remain accurate and unchanged.
No definition used by a target changes meaning and no target statement review is reopened.

## Users

A direct import scan of both live library roots and both quarantine roots finds the
following consumers (all archived at the time of inspection). None is edited. Ordinary
importers receive exactly the archived theorem interface; import-all consumers also receive
the same private helpers. No consumer adaptation or additional claim is necessary.
The restored module compiled against the published dependency build in 37.1 seconds,
without errors or warnings. The delivery tool performs the independent axiom probe.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.Paper.CondensedConstructibleOneStep | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.Paper.IntegralTensorShriek | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not queried; unchanged consumer | Archived importer; identical restored interface and private helpers, no adaptation. |

## Status

landed 20261021T020051-L-2580496 2026-10-21 (merge of deliver/A3/Sheaf.Paper.CondensedOpenClosedRecollement)
