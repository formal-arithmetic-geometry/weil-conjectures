# Delivery report: `lem-weil-pbc-descend-finite`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-descend-finite.json`: statement split and proof expanded into five source-backed steps.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-finite-stage.json`: new statement node for Stacks 01ZN; Mathlib verdict: no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-colimit-finite-algebra.json`: new statement node for Stacks 07RG; Mathlib verdict: no match.

## Attachments

No Lean declarations attached; the item has no Lean declaration in either audit.

## WANTED

None.

## Review notes

The imported node cited Stacks 01ZO but had no proof steps. The source proof first descends affineness (01ZN), then reduces over a finite affine cover to affine rings, and finally applies the directed-colimit finite-algebra lemma (07RG). Both omitted lemmas are now explicit DAG nodes. Existing nodes cover finite morphism permanence, affine finite covers, local finite type on affine pairs, and affine inverse-limit coordinates. The unit route is unchanged.

## Unfinished

No remaining work for this item. The new nodes are intentionally unsplit and enter the Stage 1 queue.

## Review by F1

I checked all five proof steps against Stacks Limits Lemma 01ZO: affine descent uses 01ZN, the finite affine-cover reduction is explicit, and the affine algebra conclusion uses Algebra Lemma 07RG. The two new nodes have complete statements, correct chapter/unit route, and LeanSearch, LeanFinder, and Mathlib grep records with no-match verdicts. The delivery contains only the assigned item, its two created nodes, and its report.
