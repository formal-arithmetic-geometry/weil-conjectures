# Stage-1 worker report: det-pe-wcb-cover

## Files written

- `dag/nodes/sec-proetale-coefficients/det-pe-wcb-cover.json` — item split into three proof steps; no new nodes.
- `citations.json` — verbatim statement quotes for every cited node and step.

## Attachments

None. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` states the full covering-and-factorization item. The source ring theorem `WContractification.IsWContractibleRing.exists_isWContractibleRing` only gives the ring-level existence and does not state this item for an arbitrary pro-étale object or its affine-open factorization.

## WANTED

None.

## What I checked

I read the target node, the current blueprint node and proof (`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-pe-weakly-contractible-basis/det-pe-wcb-cover.md` and its `.proof.md`), the pro-étale site definition, and the source-library ring construction in `WeilConjectures/RingTheory/ProEtale/WContractible.lean`. I also read every cited DAG statement. The first step now uses the strict w-local cover for its faithful-flat, ind-étale and local-ring properties; the w-strict-local definition to justify the second-stage hypothesis; the second-stage theorem for the faithfully-flat ind-Zariski map and w-contractibility; ind-étale stability for the composite; and the faithful-flat definition for the exactness argument showing faithful flatness of the composite. The second step cites the affine ind-étale to weakly étale implication, open-immersion étaleness, the site’s object condition, and weakly étale composition. The third step cites the pro-étale covering definition and the faithful-flat spectrum-surjectivity lemma; for an affine test open W, W itself is one of the chosen affine opens, the pullback is the same affine spectrum, and one index satisfies the finite refinement condition.

I checked hypotheses at each use: the strict cover is applied to each commutative ring B_i; the second stage is applied only after its output gives C_i w-strictly local; the affine ind-étale comparison is used only for Spec D_i -> Spec B_i; the open immersion is Spec B_i -> U; and the site object hypothesis supplies U -> X weakly étale. I tested the covering argument on an empty affine open (the finite family may have zero members) and on a one-affine-open object, where the single faithfully flat map is exactly the required cover. The imported unused citation to `lem-trf-weakly-etale-between-objects` was removed because its statement concerns morphisms between two already weakly étale objects and is not the factorwise composition fact needed here.

## Not duplicates

No new nodes were created, so no duplicate pairs arise. Existing nodes were reused after searching their statements and the DAG by the relevant notions and Stacks tags.

## Review by Q22

I checked the item against the current main-20261015 blueprint proof paragraph by paragraph and checked the source labels for the strict cover (Stacks 097X), the Stonean/second-stage construction (Stacks 097D/0983), weakly étale stability (Stacks 094T), and the pro-étale covering definition (Stacks 0989). I opened each cited node and copied its full verbatim statement into `citations.json`; each quote covers the hypotheses and conclusion of the non-elementary dependency used by the step. The first step’s faithful-flat composition is written out using the exactness criterion rather than asserted by “transitivity”; the second step names all three weakly étale factors and the composition theorem; and the third step explicitly identifies the pullback over W and invokes spectrum surjectivity. No new node or Lean attachment was found, and the item’s Mathlib searches were run with `msearch.py` and recorded in the node.

## Second reading by Q22

- Item statement: checked against the current `main-20261015` blueprint node and the source construction in Stacks Tags 097X, 097D, 0983, 094T, and 0989; every hypothesis and both clauses (w-contractible affine cover and affine factorization with faithfully flat ind-étale ring map) are retained. Verdict: PASS.
- Step 1: checked against Stacks 097X (strict w-local cover) and 0983 (Stonean second stage), and against the full statements of `lem-weil-pbc-strict-w-cover`, `det-pe-wlocal-strict-contractible`, `det-pe-wc-cover-second-stage`, `lem-weil-pbc-ind-etale-stability`, and `def-weil-pbc-faithfully-flat-ring-map`; the faithful-flatness composition is explicitly reflected through exactness. Empty affine opens and a zero ring are allowed. Verdict: PASS.
- Step 2: checked against Stacks 094T and the pro-étale site object definition; the affine ind-étale map, open immersion, and given object map are each weakly étale, and composition uses the exact existing node `lem-weil-pbc-weakly-etale-composition-base-change`. Verdict: PASS after citation repair.
- Step 3: checked against Stacks 0989 and the full statements of `def-weil-pbc-proetale-covering` and `lem-weil-pbc-faithfully-flat-surjective-spectrum`; for each affine test open, the corresponding single index and the affine source itself give the finite refinement, including the empty and one-open cases. Verdict: PASS.
- New nodes: none; therefore B1--B7, duplicate checks, and Mathlib-leaf checks are vacuous. Existing Mathlib leaf `lem-weil-pbc-weakly-etale-composition-base-change` was reused rather than creating a node.
- Changes made: replaced the incorrect Step 2 citation to `lem-weil-pbc-ind-etale-stability` with the exact weakly étale composition leaf; regenerated every citation entry as the complete verbatim cited-node statement; updated the split summary and this second-reading record.

