# AlgebraicGeometry.Scheme.finite_etale_trace_image

## Reason

Restore the quarantined trace-image module assigned by coord/rework.tsv after the
2026-10-22 upstream sync. Its proof calls finiteEtaleTrace_section_sum_descent in
AlgebraicGeometry.Scheme, but the archived file imports the separate étale-site
module in WeilConjectures rather than the pro-étale module that declares it.
The corrected private import supplies exactly the existing DAG proof dependency.

## Old

```lean
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSectionDescent
```

## New

```lean
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceSectionDescent
```

All declarations, definitions, theorem signatures, attributes, public imports and
proof bodies are verbatim those of the quarantine archive. The module is restored
to lean/Sheaf/AlgebraicGeometry/FiniteEtaleTraceImage.lean; the archive is preserved.
The existing node attachment and proof dependencies remain accurate and unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage | D4 (assigned rework) | Restored with the correct private descent import; compiles in 13.7 s. |
| Sheaf.Paper.ContinuousFiniteEtaleTraceLattice | unclaimed | Mentions the theorem in its proof docstring only; no code or signature changes. |

The downstream.py query reports unknown module because the item is quarantined.
A direct rg search of lean/Sheaf, lean/WeilConjectures and quarantine/Sheaf found
no current Lean importers or code references outside the archived item. The
ContinuousFiniteEtaleTraceLattice docstring is the only external name reference.
This does not justify withdrawal: the DAG and unit route still need the item.
No consumer adaptation is required because the original public API is restored.
No target statement or definition changes meaning.

## Status

landed 20261022T113913-L-389286 2026-10-22 (merge of deliver/D4/Sheaf.AlgebraicGeometry.FiniteEtaleTraceImage)
