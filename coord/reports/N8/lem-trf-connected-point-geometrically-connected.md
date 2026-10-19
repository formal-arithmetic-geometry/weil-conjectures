# Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-connected-point-geometrically-connected.json`: item, statement node split into two proof steps; no Mathlib exact match.
- `dag/nodes/sec-trace-formula/lem-trf-geometrically-connected-image-criterion.json`: new statement-only Tag 056R node; Mathlib searches found no exact match.
- `citations.json`: verbatim citations for every node used by every item proof step.

Attachments: none. I searched the read-only slopmaster2 source for the item id, its Stacks label, and the notions “connected point” and “geometrically connected”; no sorry-free project declaration states this item exactly. The existing declaration `AlgebraicGeometry.GeometricallyConnected.of_connectedSpace_of_isSepClosed` belongs to the existing node `lem-weil-separably-closed-geometrically-connected`, but its separably closed base-field hypothesis is different and it is not an attachment for this item.

WANTED: none.

The imported item had an empty proof. I kept its statement and source (Stacks Varieties Tag 04KV). The split follows the source's actual proof: first apply the field-extension theorem of Tag 037P to the residue field and use irreducible-implies-connected after every base change; then apply the connected-image criterion of Tag 056R. The Tag 056R criterion was absent from the DAG, so I added it as a strictly smaller unsplit statement node rather than silently treating the citation as elementary. The Tag 037P theorem is an existing node in another unit and is declared as a tool use because it supplies the field-theoretic input that this unit does not state. No statement correction was needed. Small cases checked conceptually: a rational point is the case `kappa(x)=k`; a purely transcendental field `k(t)` satisfies the relative algebraic-closedness hypothesis; and a disconnected scheme fails the conclusion even when one component contains such a point.

## Not duplicates

- `lem-trf-geometrically-connected-image-criterion` vs `lem-weil-separably-closed-geometrically-connected`: the new node is the Tag 056R morphism criterion over an arbitrary field and connected target; the existing node assumes the base field is separably closed and gives an iff for one scheme.
- `lem-trf-connected-point-geometrically-connected` vs `lem-sbc-connected-rational-point-geometrically-connected`: the item allows a point whose residue field is merely relatively algebraically closed (including transcendental extensions), while the existing node is only the rational-point special case and has a section hypothesis.

## Review by N8

I read `literature/stacks-project/varieties.tex` at Tag 04KV, including the proof paragraph beginning “Set T = Spec(kappa(x))”, and Tag 056R at the connected-point criterion. I also read the existing DAG statements for `lem-zl-field-extension-algebraically-closed-geometric`, `lem-pc-irreducible-space-connected`, and `def-pc-geometrically-irreducible`; each says exactly the fact cited in Step 1. The Tag 037P hypothesis matches “k is algebraically closed in kappa(x)”, and its conclusion gives geometric irreducibility of the residue-field spectrum. The irreducible-to-connected node applies after each field extension, and the geometric-connectedness definition supplies the quantified base-change conclusion. In Step 2, the new node's statement exactly supplies Tag 056R: a geometrically connected source over a connected target forces the target to be geometrically connected. The item hypotheses provide that the canonical residue-field point maps to the connected scheme X over k.

I checked the statement on the rational-point case, the purely transcendental case `k(t)`, and a disconnected union as an edge case. I checked all new ids against the DAG and searched the full blueprint for duplicates; no existing node states Tag 056R. I ran the required Mathlib searches (LeanFinder, Loogle, grep, and LeanSearch) for both the item and the new criterion; the logs are in `searches.jsonl`, and no exact Mathlib theorem was found. The server `check_dag` preflight passed before this report was written.

What remains unfinished is the proof of the newly created Tag 056R node itself; it is intentionally statement-only and therefore remains `unsplit` in the queue, as required for a one-level stage-1 split.
