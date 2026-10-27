# AlgebraicGeometry.Scheme.finite_etale_trace_image

## Reason

Restore the quarantined module assigned in coord/rework.tsv after upstream sync
58206abfd. The archive imports the étale-site descent module, but its proof calls
AlgebraicGeometry.Scheme.finiteEtaleTrace_section_sum_descent, declared in the
pro-étale Sheaf module. Correct the private proof import to its existing owner.
This is the same import defect recorded after the preceding sync and repaired by
D4; the current quarantine archive again contains the incorrect import.

## Old

```lean
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSectionDescent
```

## New

```lean
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceSectionDescent
```

Restore lean/Sheaf/AlgebraicGeometry/FiniteEtaleTraceImage.lean from its archive
with exactly this replacement. Preserve the archive, every declaration and proof,
all public imports and the existing DAG attachment and proof dependencies.
The private import supplies the already recorded section-descent dependency;
there is no statement, definition or route change.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage | D2 | Restores compilation; unchanged public API. |
| Sheaf.Paper.ContinuousFiniteEtaleTraceLattice | unclaimed | Proof docstring reference only; no adaptation. |

The downstream.py query returns unknown module because this item is quarantined.
Direct searches of lean/Sheaf, lean/WeilConjectures and quarantine/Sheaf find no
Lean importers or executable references outside the archived item. The paper
module only mentions finite_etale_trace_image in a docstring. DAG parents still
need the node, so the module is restored rather than withdrawn. No consumer
requires adaptation, and no target statement or definition changes meaning.

## Status

landed 20261023T102524-L-2916435 2026-10-23 (merge of deliver/D2/Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage)
