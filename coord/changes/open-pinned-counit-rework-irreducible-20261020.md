# Open pinned counit triangle implementation reuse

## Reason

The two quarantined Sheaf modules duplicate completed adopted upstream modules.
Their stale `attribute [local irreducible] derivedPullback` is invalid because
`derivedPullback` is now an `irreducible_def`. Removing the command initially
compiled, but repeatedly elaborating the source proof can exceed 60 seconds.
Reuse the identical upstream implementations and keep the old Sheaf import paths
as public re-exports. This also avoids duplicate public declarations if a consumer
imports the old path and the upstream twin together.

For return C-92b3d, the branch was reread at `01b064b2068e`. Both active Sheaf
files are absent following upstream-sync quarantine commit `29b1c235f4`, and
their archived implementations remain available. Their differences from the
current upstream twins are still exactly those listed below. This record and
the restored compatibility modules apply to that current state; the replacement
delivery is constructed on freshly fetched `sheaf-dag`.

## Old

The source Sheaf module defines the public comparison
`AlgebraicGeometry.openPinnedHomotopySourceCompositionIso` and proves
`AlgebraicGeometry.open_pinned_source_counit_triangle`, with six private helpers.
The target defines `AlgebraicGeometry.openPinnedHomotopyTargetCompositionIso` and
proves `AlgebraicGeometry.open_pinned_target_counit_triangle`, with three private
helpers and a proof-only `import all` of the Sheaf source module.

The two public definitions and theorems are verbatim those in their adopted
upstream twins. The complete implementation diff is limited to the copyright
header, one invalid local attribute in each Sheaf copy, and the target's private
source-module import path. No public signature or definition body differs.

Both old Sheaf files contain this invalid command:

```lean
attribute [local irreducible] derivedPullback
```

## New

The source compatibility module imports:

```lean
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSourceCounitTriangle
```

The target compatibility module imports:

```lean
public import WeilConjectures.AlgebraicGeometry.OpenPinnedTargetCounitTriangle
```

The same four public declarations, with exactly the same signatures and data,
are thereby available from the Sheaf import paths without defining them twice.
The twin modules publicly import both original statement dependencies, preserving
those exports too. The two DAG `lean` records point to the upstream files and
set `existing: true`. Their statements and proof plans stay unchanged.
No adopted source-library file is edited or removed. No target review reopens.

## Users

Textual imports and declaration users were checked in `lean/` and quarantine.
`tools/downstream.py` cannot find the Sheaf source module because quarantine has
removed it from the library; direct `rg` confirms that its only quarantined
importer is the target module restored in this same packet. All other current
consumers already import the upstream twins. No external module needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle | K6 | Restore as re-export of the identical upstream implementation. |
| Sheaf.AlgebraicGeometry.OpenPinnedTargetCounitTriangle | unclaimed, same rework cluster | Restore as re-export of the identical upstream implementation. |
| WeilConjectures.AlgebraicGeometry.OpenPinnedSourceCounitTriangle | source library | Existing completed implementation, unchanged. |
| WeilConjectures.AlgebraicGeometry.OpenPinnedTargetCounitTriangle | source library | Existing completed implementation, unchanged. |
| WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction | source library | Uses upstream triangle theorems; unchanged. |
| WeilConjectures.AlgebraicGeometry.OpenPinnedTensorCounitTransport | source library | Uses upstream comparison definitions; unchanged. |
| WeilConjectures.AlgebraicGeometry.OpenPinnedTensorComparisonCoherence | source library | Uses upstream comparison definitions; unchanged. |

Both final files compile after reconciliation. A fresh consumer simultaneously
imports both Sheaf paths and both upstream paths, applies each triangle theorem
at the full signature recorded in its current node, checks all four public
declarations, and prints their axioms. All four use only `propext`,
`Classical.choice`, and `Quot.sound`; the consumer compiled on the server in
5.0 seconds. The mathematical comparisons and their canonical data are unchanged,
including empty opens and zero complexes.

## Status

landed 20261020T154047-L-3036111 2026-10-20 (merge of deliver/K6/Sheaf.AlgebraicGeometry.OpenPinnedSourceCounitTriangle)
