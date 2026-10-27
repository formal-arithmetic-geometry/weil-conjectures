# Sheaf.CategoryTheory.TwistedSiteSieveGeometry public imports

## Reason

The file uses Mathlib's Sieve, GrothendieckTopology and sheaf condition, already
publicly supplied by InternalActionSitePresentation. It does not use the extra
IsGrothendieckTopos predicate defined in GrothendieckTopos. Remove that unused
public import after proving the complete geometry theorem.

## Old

```lean
public import Sheaf.CategoryTheory.InternalActionSitePresentation
public import Sheaf.CategoryTheory.Sites.GrothendieckTopos
```

## New

```lean
public import Sheaf.CategoryTheory.InternalActionSitePresentation
```

Every existing declaration signature and construction is unchanged. New helpers
are private and all their proofs are complete.

## Users

Read-only command: tools/downstream.py Sheaf.CategoryTheory.TwistedSiteSieveGeometry
--uses IsGrothendieckTopos. It reports one downstream module, zero uses of that
predicate. The downstream module's original source already directly imports
Sheaf.CategoryTheory.Sites.GrothendieckTopos as a proof import.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.TwistedModulePresheafEquivalence | unclaimed at audit | No edit necessary: its own explicit GrothendieckTopos import remains and its signature uses none of that module's declarations. |

No target statement or definition changes its meaning; no target statement review
is reopened. No consumer adaptations are necessary.

## Status

landed 20261023T131558-L-2123787 2026-10-23 (merge of deliver/J7/Sheaf.CategoryTheory.TwistedSiteSieveGeometry)
