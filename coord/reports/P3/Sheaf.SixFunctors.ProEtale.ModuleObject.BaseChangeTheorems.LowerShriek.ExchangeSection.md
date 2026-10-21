## What changed

Restored the quarantined assigned module
`Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection`
with its original public signature and imports. The implementation reuses ExchangeMono's
proved `sharedBoundedOpenUnitIsIso` instead of repeating the derivation of that fact.
The existing `boundedCartesianCounit` helper supplies the other geometric input.
Rewriting by the supplied equality makes the exchange component a composite of
isomorphisms; `IsIso.inv_hom_id` proves the required section equation for its inverse.
Updated the existing node's proof and proof dependencies to match this reuse.
The unit's route is preserved and the quarantined source is not deleted.

The archived source compiled in 6.9 seconds; the simplified implementation compiled
in 2.9 seconds without warnings or errors. Loogle confirmed `IsIso.inv_hom_id`;
LeanFinder returned no relevant geometric shortcut; Mathlib and library text searches
confirmed the existing ExchangeMono helpers are the shortest available route.
Import-direction checking passed. The consumer scan also included quarantine.

Change record: `coord/changes/P3-restore-open-shriek-exchange-section.md`.

## Proved and sorry left

The restored declaration
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekBaseChange_app_section`
(node `stage3-sfb-open-base-change-component-section`) has a complete proof.
This is a quarantine restoration of an already proved theorem: 0 original holes,
0 holes closed, 0 holes added, 0 holes remaining, and 0 split off.
No definition data is chosen from an unproved existence theorem.

## No longer needed

No module, declaration or import is withdrawn. ExchangeMono supplies both shared inputs,
so the direct proof dependency on `lem-weil-pbc-condensed-open-closed-recollement` is
redundant in this node and removed. That node and its module remain needed transitively
by ExchangeMono; this delivery does not claim they are pruned. The local duplicated unit
proof is replaced by its existing shared helper. Both original imports remain necessary.

## Where the brief, the DAG or earlier work was wrong

The assigned live file is absent because its cluster restoration was reverted, as recorded
in `coord/rework.tsv`; the archive has zero sorry holes. This delivery restores that
implementation rather than treating the absence as a withdrawal or introducing a new
statement. ExchangeMono has since been restored and its shared unit helper also eliminates
the archived proof's duplication. No mathematical statement or unit route was wrong.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
