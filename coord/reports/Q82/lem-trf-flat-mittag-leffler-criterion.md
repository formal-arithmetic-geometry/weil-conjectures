Files written:
- `dag/nodes/sec-trace-formula/lem-trf-flat-mittag-leffler-criterion.json` — statement, split proof, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-flat-ml-minimal-support.json` — statement-only supporting lemma (Tag 0AS6), no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-flat-ml-dual-criterion.json` — statement-only supporting lemma (Tag 059G), no Mathlib match.
- `citations.json` — verbatim statement quotes for every cited node and step.

Attachments:
- None. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `/home/ubuntu/weil-newtargets-master/WeilConjectures` states the item or either supporting lemma.

WANTED:
- None. The cited Stacks source is present in `literature/stacks-project/algebra.tex`.

What was wrong or changed:
- The imported item had no proof split. Its statement agrees with Stacks Tag 059S, including the flatness hypothesis, finite-free test module, and least-element condition.
- The source invokes two non-elementary supporting facts that were absent from the DAG: Tag 0AS6 (`lemma-minimal-contains`) and Tag 059G (`remark-flat-ML`). They are added as statement-only nodes after whole-DAG and blueprint searches found no duplicates.
- The source's finite-free Hom/tensor coordinate identification and the containment argument are written as elementary steps, with the finite-basis calculation made explicit. The stabilization step cites the existing tensor-colimit and filtered-colimit elementwise nodes.
- All Mathlib searches were run through `msearch.py` and recorded in `searches.jsonl`; the hits were general flatness or inverse-system results and did not state these claims.

What could not be finished:
- No unfinished proof or attachment remains. Lean files and compiler/build tools were not used, per the stage-1 restriction.

## Not duplicates
- `lem-trf-flat-ml-minimal-support` vs `lem-trf-flat-mittag-leffler-criterion`: the new node is the supporting lemma for arbitrary ambient modules and also proves finiteness; the item is an equivalence restricted to finite free test modules and does not assert the arbitrary-module lemma.
- `lem-trf-flat-ml-dual-criterion` vs `lem-trf-mittag-leffler-eventual-domination`: Tag 059G gives the sufficient dual inverse-system criterion for a flat finite-free presentation; the existing node states an eventual-domination equivalence and does not state this dual criterion.

## Review by Q82
I read the item source at `literature/stacks-project/algebra.tex`, Tag 059S, and the supporting source paragraphs for Tag 0AS6 (`lemma-minimal-contains`, lines 21534–21567) and Tag 059G (`remark-flat-ML`, lines 21117–21131). I also read the chapter and unit records, the imported node, and every existing DAG node cited by the split. Step 1 uses exactly the least-support statement of the new 0AS6 node, with its flat and Mittag-Leffler hypotheses checked. Step 2 uses the flat-module definition, the existing exactness leaf, and the existing Lazard finite-free colimit statement; I verified that flatness supplies the exactness hypothesis Lazard requires. Steps 3 and 4 are the finite-basis Hom/tensor coordinate calculation and the compatibility/minimality argument from Tag 059S, so they are marked elementary and cite no hidden theorem. Step 5 uses exactly the existing tensor-commutes-with-colimits and filtered-colimit elementwise statements to produce a stage containing the least coefficient submodule, then compares it with the coordinate-minimal `Q_j`. Step 6 uses exactly the new 059G dual criterion after the `Q_j` stabilize. I checked edge cases such as rank-zero finite free modules, zero modules, empty tensor elements, and arbitrary (possibly non-Noetherian) commutative rings. The longest step is a single colimit stabilization argument; it contains no separate omitted lemma. The blueprint ancestry and route remain the imported `lem-trf-local-term-locality` chain.
