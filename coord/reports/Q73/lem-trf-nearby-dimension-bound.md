# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-nearby-dimension-bound.json`: existing item, now split into three proof steps; statement, dependencies, source and inherited Mathlib search records retained; no new nodes or Mathlib leaves.
- `citations.json`: five verbatim statement quotations covering every cited node in every proof step.
- `report.md`: this report.

## Attachments

None. I searched both read-only `WeilConjectures/` source trees for `lem-trf-nearby-dimension-bound`, nearby-cycle terminology, and the statement's distinctive dimension-bound phrases. No sorry-free project declaration states the item. The existing source declarations are not attachments for this item.

## WANTED

WANTED: `literature/orgogozo-modifications-cycles-proches.pdf`, Proposition 2.3, pp. 3--4, for the uniform nearby-cycle bound and its bounded-complex truncation consequence. The node records the author PDF URL; no archival local copy is present. The existing Gabber input records its own WANTED Illusie source.

## What was checked and corrected

The imported item was a statement-only node with an empty proof. Its sheaf clause is covered by the existing, stronger node `lem-trf-gabber-nearby-cycle-dimension-bound`, which assumes only locally finite type and a bound on scheme-theoretic fibre dimensions and explicitly drops Noetherianity, invertibility and quasi-compactness. I used that node after arbitrary base change, observing that finite type implies locally finite type and geometric fibre dimension is unchanged by residue-field extension. The bounded-complex clause is then proved by the canonical truncation triangles and induction over the finite cohomology interval; no new node was created because that conclusion is a clause of this item.

The inherited Mathlib searches were retained and read. They find no nearby-cycle or cohomological-dimension theorem in Mathlib. I also searched the DAG and blueprint for a duplicate of the whole bound, a base-change fibre-dimension node, and a bounded-complex clause; the only relevant existing theorem is the Gabber sheaf bound cited above. No statement correction was needed.

## Review by Q73

I read the complete item node, its unit and chapter records, the source place recorded for Orgogozo Proposition 2.3, the full statement of `lem-trf-gabber-nearby-cycle-dimension-bound`, the definition `def-trf-oriented-nearby-cycles`, and the full statement of `lem-weil-pbc-truncation-triangle`. Step 1 cites the Gabber statement for exactly its clause that every sheaf has vanishing cohomology sheaf above twice the fibre bound; I checked that the item’s base-change morphism remains locally finite type and that the geometric fibre dimension hypothesis supplies the required scheme-fibre bound. Step 2 cites the same Gabber clause for each cohomology sheaf and the truncation-triangle statement for the distinguished triangle with graded piece $H^q(K)[-q]$; the definition of nearby cycles supplies exact total right derivation. Step 3 uses the same finite family of truncation triangles and the long exact cohomology sequences to propagate the interval bounds. Each citation quote in `citations.json` is a verbatim substring of the cited statement.

I checked edge cases $d=0$, $a=b$, the zero sheaf and zero complex, empty fibres, identity base change, and an arbitrary non-Noetherian base change. The argument gives the same bound in all cases. No SGA source is used, no Lean or compiler command was run, and no proof step hides a separately reusable lemma beyond the existing cited nodes.

## What could not be finished

No mathematical part of the split remains unfinished. The archival Orgogozo PDF is unavailable locally and is recorded as WANTED above.
