# Stage-1 report: lem-coef-symmetric-operadic-base-matching

## Files written

- `dag/nodes/sec-six-functors/lem-coef-symmetric-operadic-base-matching.json`: repaired split statement; no new nodes.
- `citations.json`: verbatim citations for every dependency used by every proof step.

## Attachments

None. I searched the slopmaster2 source for the item id, its title, and the matching terminology; no declaration states this item.

## WANTED

- WANTED: an archived copy of Lurie, *Higher Algebra*, Theorem 3.1.2.3 proof (printed pp. 334–337), for the finite pointed-chain normal form, five matching classes, and the (F(k)) filtration. The online HA PDF is cited as the source, but no copy is present in `literature/`.

## What I checked and changed

The imported node had the full theorem statement but no proof, no status, and an unspecified blueprint location. I preserved its mathematical content while adding the active/inert statement dependency, filled the blueprint ancestry and exact HA proof location, and supplied seven proof steps. Steps 1–2 establish the unique increasing strongly-inert/active factorization and reduce simplices to unique nondegenerate chains. Steps 3–5 give the exhaustive/disjoint active-seed, neutral-pair, and output-pair classification, including the (s=0) nullary case. Step 6 derives (F_0), monotonicity, exhaustion, and the stage-(k) generators; Step 7 checks degreewise inverse-image stability. The finite pointed-map arguments are written out rather than delegated to a clause-sized node. I checked the active/inert hypotheses against `lem-coef-operadic-approximation-restriction`, the nerve convention against `def-cbc-enhanced-diagrams-cones`, and the unique nondegenerate decomposition against `lem-weil-pbc-simplicial-set-nondegenerate-decomposition`; each citation quote is copied verbatim into `citations.json`. The small cases (s=0), empty active blocks, empty strongly-inert tails, and arbitrary initial coordinate-zero blocks are explicitly handled. The item’s existing Mathlib searches were read and remain recorded; they found no matching Mathlib theorem.

## Repair of returned points

I repaired all five numbered issues in the return. The malformed control characters in Step 1 were replaced by the literal TeX symbols \rho' and \beta', and the uniqueness conclusion now reads \beta'=\beta. The statement now cites `lem-coef-operadic-approximation-restriction` for the active/inert convention, and says explicitly that arbitrary prefixes occur only in the two neutral classes. Step 3 now classifies by the letter immediately before the longest suffix with word A^*S^*, rather than by the first neutral edge; it explicitly tests the previously missed words NSA and NN. Step 6 says that dimension-(k-1) seeds enter through the all-simplices-of-dimension-<k clause, while the dimension-k longer partners are the added generators, removing the dimension slip. Step 7 no longer claims that inverse image commutes with generated closure: it uses only degreewise pullback, inclusions, unions, and successive degreewise differences. I reread the three cited dependency statements and the HA proof location after these edits, and the citation quotes remain verbatim.

## Review by Q131

I reread the item and the cited source material: the finite pointed-map active/inert convention in `lem-coef-operadic-approximation-restriction`, the nerve definition in `def-cbc-enhanced-diagrams-cones`, the unique nondegenerate decomposition in `lem-weil-pbc-simplicial-set-nondegenerate-decomposition`, and Lurie Higher Algebra Theorem 3.1.2.3, printed pp.334-337. The item statement now names the approximation node for inertness and limits the arbitrary-prefix wording to neutral classes; all other hypotheses and clauses agree with the imported statement. No new node was created, so there is no new-node source or duplicate pair to review.

Step 1 uses exactly the approximation statement's definitions of inert and active; its construction retains precisely the nonbasepoint inputs and proves uniqueness, with the repaired literal symbols \rho' and \beta'. Step 2 uses the enhanced-diagrams nerve statement and the nondegenerate-decomposition statement. Step 3 uses the same active/inert definitions and now checks the longest A^*S^* suffix, including NSA and NN, so the five classes are exhaustive and disjoint without the false first-neutral-edge claim. Step 4 uses the factorization supplied by Step 1 and the corrected distinguished strongly-inert edge immediately before the nonempty active block. Step 5 uses the active/inert convention for the color projections and checks the s>0 and s=0 cases. Step 6 uses the degreewise simplicial-product statement and nondegenerate decomposition; it now distinguishes dimension-(k-1) seeds (included by the <k clause) from dimension-k longer partners. Step 7 uses only the degreewise pullback statement: inclusions, unions, and successive degreewise differences are preserved, and it deliberately makes no claim that inverse image commutes with generated closure.

I checked the hypotheses and edge cases by hand: the neutral maps with words NSA and NN, the neutral map <3>→<2> sending 1↦2, 2↦*, 3↦1, empty active or strongly-inert blocks, final arity s=0 and s>0, the all-active closed seed, and arbitrary initial coordinate-zero blocks. The report, citations, blueprint metadata, and existing Mathlib search log were retained and updated only to describe these repairs.

## Not duplicates

No new nodes were created, so there are no duplicate-node pairs to report.
