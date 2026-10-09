# Stage 1 report: `lem-weil-pbc-stein-geometric-fibre-etale-criterion`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-stein-geometric-fibre-etale-criterion.json`: split the Tag 03GZ criterion into the fibre/base-change identification, the forward implication, and the finite-separable converse.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-geometrically-connected-finite-separable-test.json`: new public unsplit statement for Varieties Tag 0389.
- `coord/reports/G1/lem-weil-pbc-stein-geometric-fibre-etale-criterion.md`: this report.

## Sources and dependencies

The parent follows More on Morphisms Lemma 37.53.6 (Tag 03GZ), proof lines 15221--15233. The forward direction uses the existing scheme fibre/base-change conventions and the reviewed etale residue-field separability node (Tag 02G8). The converse cites the new public Tag 0389 node and the existing etale neighbourhood realization node (Tag 02LF). No private proof lemma or imported module was introduced.

The new 0389 node is statement-only while unsplit, introduces all of its objects, records the exact source place and Stacks tag, and records LeanSearch, LeanFinder, and grep searches. Mathlib has no finite-separable geometric-connectedness equivalence.

## Review by G1

I checked the parent statement against More on Morphisms 03GZ. For an etale point, the residue extension is finite separable by the existing reviewed 02G8 node, and associativity of the scheme fibre/base-change definitions gives the displayed fibre identification. Geometric connectedness therefore gives the forward implication by its definition. For the reverse implication, the new 0389 node supplies a finite separable extension producing a disconnected base change when geometric connectedness fails; the existing 02LF node realizes that extension as the residue field of an affine etale neighbourhood, so the assumed connectedness of every such fibre is contradicted. Each non-elementary step names its DAG inputs, all new metadata carries chapter `sec-proper-base-change` and unit `sk-thm-p1`, and the new child has `created.item` equal to this item. `review_split.py`, `check_dag.py --cycles`, and `git diff --check` pass; the nine reachability messages are pre-existing repository warnings.

## Incomplete work

The finite-separable test remains unsplit for a later Stage 1 worker. No Lean was written or compiled.
