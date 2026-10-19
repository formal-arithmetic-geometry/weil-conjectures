# Worker report: prop-weight-purity

## Files written

- `dag/nodes/sec-zeta-weil/prop-weight-purity.json`: statement node, split; no new node and no Mathlib leaf.
- `citations.json`: one verbatim citation for the single proof step.
- `report.md`: this report.

## Attachments

None. No finished declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` states the item exactly. The existing DAG declaration `thm-weil-deligne-purity` is used as the proof dependency because its statement includes the item as assertion (1); it is not an attachment of the item.

## WANTED

None.

## What was checked and corrected

The item statement was compared with `literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-input-weights/prop-weight-purity.md` and its proof file, and with the imported master snapshot. The statements are identical, including the exceptional-adjoint admissibility, canonical dualizing Weil lift, scalar-extension identifications, Frobenius convention, and conclusion. The source checkout was searched by the item id, its title and the blueprint tag; no sorry-free project declaration states this exact proposition. The current blueprint proof has one argument: identify the constant Weil sheaf with the smooth-proper purity interface and read assertion (1) from `thm-weil-deligne-purity`. I retained that route and cited only the existing theorem.

## Review by Q156

I opened the full statement of `dag/nodes/sec-zeta-weil/thm-weil-deligne-purity.json`. Its first assertion says verbatim `1. the constant Weil sheaf $(\Qlb)_X$ is $\iota$-pure of weight $0$;`, which is the conclusion used by step 1; this exact sentence is recorded in `citations.json`. The step does not use any unstated hypothesis beyond the item’s already fixed smoothness, properness, geometric connectedness, coefficient and geometric-Frobenius data, and it uses no hidden construction from the theorem’s proof. I also checked the full item statement against both blueprint snapshots and the theorem’s corresponding hypotheses. The existing theorem is a larger bundled statement in the same unit, so no duplicate or clause node was created and no cycle is introduced.

The item was searched twice with each required Mathlib search family. LeanFinder and LeanSearch returned only unrelated sheaf, modular-form, condensed, or Witt-vector declarations; Loogle reported unknown project identifiers; and Mathlib grep returned no hits. These eight searches are recorded in the node with their exact query text and in `searches.jsonl`. Small edge cases are covered by the cited theorem’s universal assertion, including dimension `d=0` and the allowed degree range. No source error or unresolved dependency was found.

## What could not be finished

Nothing remains for this split; the required dry run is the next step.
