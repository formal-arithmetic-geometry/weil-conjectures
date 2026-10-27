# AlgebraicGeometry.tensorResolutionChartHomologyIso_naturality

## Reason

Repair the return of 9f5dc5c71d3 by taking the current item file as the starting
point. It already publicly re-exports the canonical upstream implementation.
The DAG still points to the compatibility wrapper with existing = false, so its
attachment incorrectly locates the declaration. Record the canonical implementation
and keep the existing compatibility API. This is a zero-hole repair.

## Old

Current compatibility file, verbatim:

```lean
/- Copyright (c) 2026. All rights reserved. -/
module

public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturality

/-! # Affine tensor-homology naturality

Compatibility import. The adopted upstream module
`WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturality`
states and proves the same
declarations under the same names, so this path re-exports it instead of keeping a
duplicate copy.

Source: Stacks Project, Tags 08DX(2), 06YT and 01I9.
(blueprint: new-t3-qcoh-tensor-resolution-chart-homology-naturality).
-/
```

The node's lean record has existing = false,
module = Sheaf.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturality and
file = lean/Sheaf/AlgebraicGeometry/QCohTensorResolutionChartHomologyNaturality.lean.

## New

Current compatibility file with the standard public-section header:

```lean
/- Copyright (c) 2026. All rights reserved. -/
module

public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturality

/-! # Affine tensor-homology naturality

Compatibility import. The adopted upstream module
`WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturality`
states and proves the same
declarations under the same names, so this path re-exports it instead of keeping a
duplicate copy.

Source: Stacks Project, Tags 08DX(2), 06YT and 01I9.
(blueprint: new-t3-qcoh-tensor-resolution-chart-homology-naturality).
-/

@[expose] public section
```

The node's lean record has existing = true,
module = WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturality
and file = lean/WeilConjectures/AlgebraicGeometry/QCohTensorResolutionChartHomologyNaturality.lean.
Record D3 and the repair date. Keep the declaration name and complete Lean statement
verbatim: it equals the current upstream signature exactly. All other current node
fields are preserved. No source-library, target, definition or quarantine file is
changed; no declaration is removed or replaced by a hole.

## Users

The current tools/downstream.py query for the Sheaf module and
AlgebraicGeometry.tensorResolutionChartHomologyIso_naturality reports zero downstream
modules and zero uses. The source import search confirms no importer of this Sheaf wrapper.
The current coord/rework.tsv has no row for the item; the former archived path
is absent. Its live compatibility wrapper is present and is the source used for
this repair. The upstream coordinate-sections naturality module imports the
canonical implementation, and the root WeilConjectures module publicly imports it;
both stay unchanged. The existing DAG parent
new-g2-existing-qcoh-tensor-resolution-coordinate-naturality remains unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturality | D3 | Preserve current re-export; add standard header and correct its node attachment. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateSectionsNaturality | unclaimed | Compatibility API checked by scratch consumer; no edit. |
| Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonNaturality | unclaimed | Compatibility API checked by scratch consumer; no edit. |
| WeilConjectures.AlgebraicGeometry.QCohTensorResolutionCoordinateSectionsNaturality | unclaimed | Existing canonical theorem use untouched. |
| WeilConjectures | unclaimed | Existing canonical public import untouched. |

A scratch consumer imports the repaired wrapper with the two compatibility modules
above and applies the theorem to the exact DAG signature. It also checks axioms of
the theorem, the pure-tensor square, the homology-square theorem, chart homology,
chart comparison and coordinate-sections naturality. Scratch checks are excluded
from the delivered Lean modules.

## Status

landed 20261023T102526-L-2917128 2026-10-23 (merge of deliver/D3/Sheaf.AlgebraicGeometry.QCohTensorResolutionChartHomologyNaturality)
