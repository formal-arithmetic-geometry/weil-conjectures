# AlgebraicGeometry.perfectOverlapProjectionCompositionComponent

## Reason

Restore the module assigned in coord/rework.tsv from
quarantine/Sheaf/AlgebraicGeometry/PerfectOverlapProjectionCompositionComponent.lean.
Compiling that archive against the published library fails at its local reducibility
attribute: derivedPullback is already globally irreducible. Lean rejects assigning
that status again. Remove only derivedPullback from that local attribute; keep
perfectHomComposition locally irreducible. No definition or statement is changed.

The restored theorem and its private combining lemma retain their complete proofs.
Its public import of PerfectOverlapCompositeStageMap remains unchanged. Four
redundant private imports are removed; their required declarations are already
reexported by the retained imports. There are zero holes before and after this repair.

## Old

The live Lean module is absent, with its source preserved in the quarantine path
above. The archived failing line is:

```lean
attribute [local irreducible] derivedPullback perfectHomComposition
```

## New

Restore the archived module under
lean/Sheaf/AlgebraicGeometry/PerfectOverlapProjectionCompositionComponent.lean,
with the same theorem signature, universes, instances, visibility and proof, and:

```lean
attribute [local irreducible] perfectHomComposition
```

Remove the redundant private imports DerivedPullbackComposition,
PerfectOverlapNestedPullbackSquare, PerfectOverlapObjectRealizationCoreComparisons
and PerfectOverlapStageEquivalence. The remaining public and private imports suffice;
the final file compiles without warnings in 11.8 seconds through lcompile.py.

## Users

The live downstream.py query reports an unknown module because this item is
quarantined. A source scan of live lean/Sheaf and lean/WeilConjectures finds no
current consumer. The same scan of quarantine finds one archived consumer, listed
below; its call uses the identical theorem signature. The DAG parent
lem-pc-perfect-overlap-composite-object-pin still needs this theorem and its
attachment and dependencies are preserved. The unit route is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositionComponent | F3 | restored; obsolete local attribute removed |
| Sheaf.AlgebraicGeometry.PerfectOverlapCompositeObjectPin | quarantined | identical theorem signature and public reexports; no adaptation |

All changes to reducibility and instances in the restored file are local. No
consumer interface is removed, and no target statement or underlying definition
changes. This restoration does not reopen target-meaning review.

## Status

landed 20261022T011838-L-3223921 2026-10-22 (merge of deliver/F3/Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositionComponent)
