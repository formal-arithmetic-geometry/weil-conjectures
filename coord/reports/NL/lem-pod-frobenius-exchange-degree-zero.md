# Stage-1 report: lem-pod-frobenius-exchange-degree-zero

## Files written

- `lem-pod-frobenius-exchange-degree-zero.json`: statement node, split into five proof steps; no new nodes and therefore no Mathlib leaves.
- `citations.json`: verbatim statement quotes for every cited node at every proof step.
- `searches.jsonl`: the four required Mathlib searches run with `msearch.py` on 2026-10-17.

## Attachments

None. No declaration in `/home/ubuntu/weil-newtargets-master/WeilConjectures/` states this item, and the archived master source has no declaration tagged with this item id.

## WANTED

None.

## What was wrong in the node, the blueprint, or the brief

The imported node was unsplit and its historical `created.item` field names the parent constant-section item; I retained that provenance and supplied the missing proof split. The related node `lem-trf-graph-frobenius-point-exchange` is not a duplicate: it assumes properness and finite-level coefficients, whereas this item allows every separated finite-type `Y_0` and a degree-zero constructible module. The blueprint has no node stating this general degree-zero mate, so the item remains the sole statement node.

## What I could not finish

Nothing. No Lean files were written and no compiler, Lake, or build tool was run.

## Review by NL

I read the full item, the `sk-lem-finite` unit record, the `sec-poincare-duality` chapter record, the current main-20261015 and master `prop-cohomological-finiteness` blueprint texts, and the source declarations for every node cited in the five steps. Step 1 checks the Frobenius square and the exact site relabelling for scheme isomorphisms, including the constant-coefficient comparison and the directions of `j` and `lambda`. Step 2 uses the stated K-injective construction of derived direct image, the right-adjoint/K-injective lemma, and the pre-derived adjunction fraction formula to identify the specified derived exchange mate with the underived square mate; I verified that the transpose has exactly the square identification followed by the inverse-image counit appearing in `B_M`. Step 3 unfolds the point-transport definition and uses exact sections on `s` to read its degree-zero map as `Gamma(s,j) sigma`. Step 4 reads the pro-etale inverse-image colimit and its counit at the final objects; the square identification sends the inserted `h`-section to the restriction-insertion map along `g`, which is exactly `p_{g,M}`. Step 5 composes these equalities using `(lambda^h)^{-1}=j^h` and the definition of `tau_M`; exact sections justify passage from sheaves to sections. I checked the edge cases `M=0`, `Y=Spec k`, `g=id`, and disconnected `Y`; all maps remain objectwise and no properness, connectedness, Weil structure, or selected unit section is introduced. Every proof step is below 2000 characters and `proof_deps` is exactly the union of its `uses`.
