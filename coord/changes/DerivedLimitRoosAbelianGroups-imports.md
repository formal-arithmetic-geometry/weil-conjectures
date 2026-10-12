# DerivedLimitRoosAbelianGroups imports

## Reason

OfSequence provides constructors used only in proofs/private helpers here. The brief
requires that import to be plain import. Public Category.Preorder retains the index
category needed by the unchanged public statements. The new positive-degree module
also needs only Category.Preorder, not the sequence constructors.

## Old

```lean
public import Mathlib.CategoryTheory.Functor.OfSequence
```

## New

```lean
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Functor.OfSequence
```

In the new positive-degree module only the first line is needed. No existing
signature, definition body, target statement or mathematical meaning changes.

## Users

Ran tools/downstream.py with --direct --uses ofOpSequence ofSequence
ofOpSequence_app: seven direct importers. MilnorSequence is the only constructor
user among these; it already directly imports OfSequence for its proofs (line 13).
All others use the public tower declarations, whose signatures remain unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.DerivedLimitEventuallyIso | unchanged, no adaptation required | No sequence constructor use; public signatures unchanged. |
| Sheaf.CategoryTheory.SurjectiveTowerLimitAcyclic | unchanged, no adaptation required | No sequence constructor use; public signatures unchanged. |
| Sheaf.CategoryTheory.Triangulated.MilnorBoundaryFactorization | unchanged, no adaptation required | No sequence constructor use; public signatures unchanged. |
| Sheaf.CategoryTheory.Triangulated.MilnorSequence | unchanged, no adaptation required | Already has proof-only OfSequence import. |
| Sheaf.Topology.DerivedLimitStalkInjective | unchanged, no adaptation required | No sequence constructor use; public signatures unchanged. |
| Sheaf.Topology.PointwiseTruncationLimit | unchanged, no adaptation required | No sequence constructor use; public signatures unchanged. |
| Sheaf.Topology.RingedSpaceRGammaDerivedLimit | unchanged, no adaptation required | No sequence constructor use; public signatures unchanged. |

## Status

landed 20261012T120919-L-980757 2026-10-12 (merge of deliver/P1/Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups)
