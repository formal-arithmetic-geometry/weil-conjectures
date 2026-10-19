## Files written

- `dag/nodes/sec-trace-formula/def-trf-oriented-constructible-sheaf.json`: existing definition copied and marked `split`; no new nodes or Mathlib leaves.
- `citations.json`: empty, because a definition has no proof steps.
- `searches.jsonl`: the four required Mathlib searches run for this item.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id, its blueprint tag, and the oriented-product/constructible-sheaf terminology. No sorry-free project declaration states this definition exactly.

## WANTED

None. The source context and all statement dependencies are present in the repository.

## What was wrong and what changed

The repository node was an unsplit imported definition with no proof. Its six dependencies (`lem-trf-oriented-product-universal`, `def-weil-sheaf-of-modules-category`, `def-weil-pbc-constant-sheaf`, `def-constructible-stratification`, `def-weil-constructible-subset`, and `def-trf-oriented-nearby-cycles`) are existing nodes and directly provide the notions used in the statement, so splitting would create only duplicate or elementary nodes. I retained the statement and source, recorded the current Mathlib search results, set the node status to `split`, and added the required split report. The searches found only unrelated ordinary sheaf, condensed-module, and constructible-topology declarations.

## Review by Q37

I read the item node, the `sk-i-curve-zero` unit and `sec-trace-formula` chapter records, and the ancestor blueprint definition/proof context for `lem-trf-local-term-locality`. I checked the statement clause by clause: the finite ring and sheaf-of-modules data use the existing module and constant-ring definitions; the two finite stratifications and constructible strata use the existing stratification and constructible-subset nodes; and each oriented stratum restriction is the inverse image along the universal oriented-product map, with finite locally constant values as stated. The nearby-cycles specialization (`Y=S`, `b=1_S`) matches the existing `def-trf-oriented-nearby-cycles` dependency. Since this is a definition, it has no proof steps and therefore no node citations; `citations.json` is correctly empty. I also checked the source declaration search and reran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py`; no Mathlib declaration matches the oriented-product notion.

All checks were performed in the isolated sandbox. No Lean files, compiler, Lake, or build tools were used.

## What could not be finished

Nothing remains for this stage-1 split.
