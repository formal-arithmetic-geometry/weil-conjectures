# Stage-1 report: prop-pod-degree-of-the-pairing

## Files written

- `dag/nodes/sec-poincare-duality/prop-pod-degree-of-the-pairing.json`: the item, split with one complete proof step; Mathlib searches found no match.
- `citations.json`: verbatim statement quotes for both cited nodes in step 1.
- No new nodes were created.

## Attachments

None. The tagged slopmaster2 declarations `degreeZeroPairing`, `degreewisePairing`, `degreewisePairing_apply`, `untwistClass`, `untwistedDegreewisePairing`, and `untwistedDegreewisePoincarePairing` are definitions or pointwise identities and do not state the full proposition under the item hypotheses.

## WANTED

None.

## Review by Q153

I read the imported item and the current `main-20261015` proposition and proof. I updated the source pointer from the old master order to order 2777 and synchronized the statement with the current blueprint, including its explicit dependency on `def-pod-derived-poincare-pairing`. I also read the statement of `def-pod-derived-poincare-pairing`: it supplies the composite defining `β_K`, with compactly supported global sections in the first variable, ordinary global sections of `K^∨(d)` shifted by `[2d]` in the second, and the mixed-support cup product, evaluation, and normalized smooth trace. The step cites this node for the degree-preserving derived pairing and its target.

The one proof step follows the source paragraph. First, it checks that the cup product, evaluation, and trace preserve degree and applies the convention `H^r(C[m]) = H^{r+m}(C)` to identify the degree `-i` piece of `RΓ(X,K^∨(d))[2d]` with `H^{2d-i}(X,K^∨(d))`; the `i=0`, `d=0`, negative-degree, and zero-complex cases are consistent with the same shift calculation. Second, it reads the coefficient twist from `def-coefficient-twists-detailed`, uses the displayed construction `K(m)=K⊗^LΛ(m)`, the invertible rank-one twist line and its inverse, and obtains the canonical identification with `H^{2d-i}(X,K^∨)⊗Λ(d)` and the line-valued map into `Λ(-d)`. The citations file quotes the exact pairing formula and twist formula from those two node statements. The source treats compatibility of the twist with global sections as part of this coefficient-twist convention; introducing a separate node for that sentence would merely restate the line-valued clause of this item, so no duplicate or clause-node was created.

I searched the complete DAG and blueprint for existing pairing, twist, and projection statements. The existing `lem-wf-constant-twist-cohomology` is restricted to the older Weil/Q̄ℓ setting and gives a different compact-support projection formula; `lem-sf-projection-finite-constant` is an étale finite-presented-constant-coefficient theorem; neither states this all-stage ordinary-cohomology identification. No source or hypothesis was silently changed, no SGA source was used, and no compiler or Lean build was run.

## Mathlib search record

The required searches for the item are recorded in `searches.jsonl`: LeanFinder and LeanSearch returned unrelated homological/group-cohomology declarations, the Loogle query was rejected for an unknown identifier, and the Mathlib source grep found no geometric Poincaré-pairing declaration. These are reflected in the item's `mathlib_searches` field.

## What was wrong or corrected

The imported item pointed to the old blueprint snapshot, omitted `def-pod-derived-poincare-pairing` from `stmt_deps` and the proof uses, and had no Mathlib search record or citations file. I corrected those metadata and citation omissions while preserving the proposition and its proof route.

## Could not finish

Nothing remains unfinished at stage 1.
