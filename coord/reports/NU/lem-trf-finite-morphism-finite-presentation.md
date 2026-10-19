# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-morphism-finite-presentation.json` — item split; no new nodes; Mathlib search found no single exact theorem.
- `citations.json` — verbatim citations for the proof step.

## Attachments

None.

## WANTED

None.

## What was checked and corrected

The item has no sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; searches for its id and for finite-morphism/finite-presentation declarations found no attachment. The imported statement agrees with Stacks Project `flat.tex`, Tag 057T: the assertion is that a finite morphism which is locally of finite presentation is of finite presentation. I retained the item's exact hypotheses and conclusion.

No new node was created. The proof uses the existing definition node `def-weil-finite-integral-morphism`, whose statement explicitly says that a finite morphism is affine; the existing Mathlib leaf `lem-weil-pbc-affine-morphism-permanence`, whose statement gives quasi-compactness and separatedness (hence quasi-separatedness) for an affine morphism; and `def-sbc-locally-finite-presentation`, whose statement defines finite presentation as local finite presentation plus quasi-compactness and quasi-separatedness. I read each cited node's statement and verified that it supplies exactly the fact used by Step 1. The local finite-presentation hypothesis is the item's hypothesis, while the other two conjuncts come from the finite and affine assumptions. The edge cases of an empty source and an empty target are covered because the affine permanence statement and the definition are unconditional.

I also read the source paragraph at `flat.tex` lines 597–633 and the cited Morphisms definitions/lemmas (Tags 01TR and 01TQ). The source's proof is exactly this short definition argument. The four Mathlib searches were run through `msearch.py` and recorded in `searches.jsonl`; they found only component declarations, so the item remains a non-Mathlib statement. No duplicate or additional dependency was introduced.

## Review by NU

I checked the source paragraph for Tag 057T and compared every clause with the item statement. Step 1 cites three existing nodes. `def-weil-finite-integral-morphism` says finite means affine, `lem-weil-pbc-affine-morphism-permanence` says affine morphisms are quasi-compact and separated (and therefore quasi-separated), and `def-sbc-locally-finite-presentation` states the exact definition of finite presentation. The item hypothesis supplies local finite presentation, so the conjunction gives the conclusion without any hidden assumption. The citations in `citations.json` are verbatim substrings of those node statements. I checked the slopmaster2 source for an exact declaration and found none, ran all required Mathlib searches, and preserved the blueprint ancestry from `lem-trf-local-term-locality`.

## What could not be finished

Nothing remains unfinished.
