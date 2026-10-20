# CartesianChartExchangeCoefficients duplicate retirement

## Reason

This is the listed `retire` item in coord/retire-items.tsv, authorized by the human's
2026-10-20 hand-off in coord/changes/retire-sheaf-twins-20261020.md. The Sheaf copy
contains zero holes and only private declarations. Its seven declaration bodies,
including the flatten definition, agree token for token with the upstream twin
when whitespace is ignored. Consumers can use the upstream implementation directly.
The upstream file is untouched.

## Old

The four direct consumers privately import the duplicate:

```lean
import all Sheaf.AlgebraicGeometry.CartesianChartExchangeCoefficients
```

The retired file declares comp_single, comp_single_inv, flatten, flatten_comp_left,
flatten_comp_right, raw_comp_named, and raw_coefficient_square, all private.

## New

The same consumers privately import the already-proved upstream twin:

```lean
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeCoefficients
```

The Sheaf copy is withdrawn in deleted.txt. No public signature, public import,
definition, theorem statement or target changes. Three existing long proof lines
are wrapped. Comments explain three existing local heartbeat settings, whose values
are unchanged. Each consumer disables the private-module linter before entering
its namespace, matching the upstream twin's header: these files intentionally
contain only privately imported proof helpers. The preexisting namespace-local
setting does not suppress the module-level warning.

No DAG node or unit points at the copy, including quarantined sources. No DAG
route changes. The four consumer import closures were scanned after migration:
no closure contains both Sheaf.Y and WeilConjectures.Y. All remaining direct
references are removed in this delivery.

## Users

The following table lists every transitive importer (source import-graph scan),
including all four adapted consumers. All four were unclaimed at preparation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeCoefficients | D2 | Duplicate withdrawn; upstream implementation retained. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeAdjunction | unclaimed | Proof import migrated; all declarations preserved. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison | unclaimed | Unchanged; no public interface affected. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeCore | unclaimed | Proof import migrated; all declarations preserved. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeEvaluation | unclaimed | Unchanged; no public interface affected. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeSource | unclaimed | Proof import migrated; all declarations preserved. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeTransport | unclaimed | Proof import migrated; all declarations preserved. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftCoherence | unclaimed | Unchanged; no public interface affected. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftNaturality | unclaimed | Unchanged; no public interface affected. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftRawNaturality | unclaimed | Unchanged; no public interface affected. |

## Status

landed 20261020T160255-L-3349679 2026-10-20 (merge of deliver/D2/Sheaf.AlgebraicGeometry.CartesianChartExchangeCoefficients)
