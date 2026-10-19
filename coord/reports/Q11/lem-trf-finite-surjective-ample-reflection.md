1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-surjective-ample-reflection.json`: item split into seven steps; statement and current main metadata unchanged; no Mathlib match.
- `citations.json`: 34 verbatim statement quotations, one for every step/cited-node pair.
- `review.md`: source and citation audit of this repair.
- Removed the unlanded proposed children `lem-trf-finite-affine-cohomology-projection` and `lem-trf-vanishing-criterion-ample`: their required inputs already exist in the current DAG. There are zero new nodes and zero new Mathlib leaves.

2. Attachments

None. The retained earlier source search found no finished project declaration for the item. In this repair I also searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag, item/child ids, finite-surjective ampleness phrases and 0B5V. No exact project theorem was found. Existing general morphism or pullback declarations do not prove the descent implication.

3. WANTED

None. All mathematical sources used here are in the local Stacks checkout.

4. Repair of returned delivery

Returned head: `b6379fc8f9`, return dated 2026-10-17 21:28 UTC. The sandbox's existing proof, report, citations and logged searches were read before editing. The first required dry run exited with a duplicate check against the current `lem-trf-ideal-twist-vanishing-implies-ample`. The current repository item is still unsplit and has the same statement and inherited ancestry as the sandbox item; its metadata is retained. The delivery tool rebases this revised packet onto current main.

- C3/C4, unstated sheaf identity: Step 4 now cites `lem-weil-pbc-affine-pushforward-ideal-product` clause (2), which literally states equality as submodules. Nothing is taken from another node's proof.
- C1/C4, coherence on Y: the same node's clause (1) supplies quasi-coherence of H as a submodule of F. `lem-weil-pbc-coherent-kernel-cokernel-locnoeth` clause (2), applied on the locally Noetherian Y, supplies coherence. Separately, `lem-weil-pbc-finite-pushforward-coherent` supplies coherence of G and of JG. Step 2 establishes the hypotheses on both schemes.
- B9, both new ancestry chains: removed both redundant children rather than leaving false ancestry records. The expected chain for either child would have been `[lem-trf-finite-surjective-ample-reflection]` followed by the item's entire ten-node `via` array, ending at `lem-trf-local-term-locality`; `[]` was incorrect. The item's full historical chain is retained unchanged, as coord/dag-sync.md requires. No new ancestry record remains.
- B5, source tag: the ordinary projection formula in Step 5 and proof_origin is correctly Tag 01E8 (`cohomology-lemma-projection-formula`). Tag 01CD is tensor-product pullback, not that theorem. The existing `lem-pc-projection-formula` supplies a general derived statement whose invertible-module clause specializes using the existing affine vanishing statement; the ordinary local calculation is also written out.
- B4, math delimiters: the malformed child statement containing escaped dollar delimiters was removed. All retained proof formulas use ordinary `$...$` delimiters and JSON contains only the necessary escaping of TeX backslashes.

The original report described two new statement-only nodes and five steps. Those descriptions are superseded by the seven-step repair above. Its sources, no-attachment conclusion, statement check and actual Mathlib search log remain retained. Searches recorded in `searches.jsonl` were read and were not repeated: the item statement and the original search questions have not changed. No new node requires a new absence claim. The item retains its imported search records; no unexecuted query has been added.

5. What I could not finish

Nothing remains unfinished in this stage-1 split. Dependencies already in the DAG may remain unsplit; the delivery does not assert their Lean completion.

## Not duplicates

No new nodes remain. The earlier projection/cohomology child is replaced by the existing ideal-product identity, coherence, finite pushforward, general projection formula and affine cohomology statements, specialized explicitly in Steps 4-6. The earlier ampleness-criterion child is replaced by `lem-trf-ideal-twist-vanishing-implies-ample`: Step 7 derives its exact ideal-twist hypothesis from P, including coherence of all quasi-coherent ideals. No new node restates the item or one of its implications.

## Review by Q11

I read delivery-errors B-E in full, the worker/stage-1 contract, the three-level rule in SETUP, GOAL, coord/dag-sync, and the chapter and unit records. I read the returned item and both proposed children, compared the item with current main, and read every cited node's statement. The full source/citation audit is in `review.md`.

For the item I read local `coherent.tex` Tag 0B5V (`lemma-surjective-finite-morphism-ample`) completely. For the removed criterion child I read Tag 0B5U (`lemma-vanshing-gives-ample`), including its proof and all three quantifier patterns. For the removed projection child I read 0B5V's full calculation, 01YP's statement and proof, 01Y1, 01Y6, 089W, and the full ordinary projection formula 01E8 in `cohomology.tex`. The tag/label pairs are checked in `tags/tags`. I retained the source route: affine ascent, cohomological-property devissage, generic support, ideal product, projection/cohomology comparison, Serre vanishing, then the converse ampleness criterion.

Step 1 uses precisely affine pullback ascent and the definitions of finite, tensor pullback and rank-one invertibility. Step 2 verifies Noetherianity for both X and Y, including local Noetherianity and quasi-compactness of the base; the finite-type theorem therefore applies. Step 3 checks all three preliminary devissage clauses. Its derived-functor theorem has the abelian/enough-injectives and additive/left-exact hypotheses supplied by explicit statements, and cohomology is identified with derived global sections by its definition. The rank-one local tensor argument verifies exactness, with the stalk-exactness statement cited. The direct-sum descent uses the first-summand retraction for r>=1, not an unsupported infinite-sum assertion.

Step 4 uses the generic-support node only for the support and annihilator it actually states. The distinct finite-pushforward statement gives coherence of G. The affine ideal-product node explicitly states both quasi-coherence of H on Y and the equality JG=f_*H. The coherent-submodule statement is applied on the Noetherian Y, and finite pushforward is applied on X, so each coherence assertion is justified. These are the two substantive missing inputs in the returned version.

Step 5 uses the invertible-module clause of the general projection formula, not its proof. The affine permanence statement gives its quasi-compact/quasi-separated hypotheses. The tensor quasi-coherence statement and affine higher-direct-image vanishing apply to H and its twist. Taking degree zero gives the ordinary projection isomorphism, and its local multiplication map and the tensor-power pullback identification are written explicitly; no independent naturality lemma is hidden. Step 6 uses the affine cohomology edge statement for the same twist. Serre vanishing applies with coherent H, proper Y over the same Noetherian R, and the ample invertible f^*L. It gives one bound for all p>0. The ideal-product stalk statement gives equality through the inclusion into G, exactly as the devissage clause requires.

Step 7 matches all clauses of the devissage statement, including its explicit zero case, and uses its conclusion for every coherent module. The Noetherian coherent criterion makes O_X coherent; the coherent-submodule theorem then makes every quasi-coherent ideal coherent. Taking n>=max(1,n0) verifies the exact hypothesis of the existing ideal-twist criterion; the final conclusion is ampleness in the same absolute sense as the item.

I checked the small cases X=Y empty (surjectivity forces X empty if Y is empty), zero sheaves, J=0 and J=O_X, n=0 in the comparison, and r=1 in the retract. No field, reducedness, dimension, flatness or projectivity assumption was introduced. For J=0 the generic-stalk condition can hold only where O_{X,xi}=0, so it is not accidentally used at a nonempty integral subscheme. All seven steps are shorter than 2000 characters; the projection specialization is a single local rank-one argument plus applications of existing statements. No new mathematical lemma is hidden by a long step.

Every node used outside the inherited unit is declared in split_report.tool_uses as a generic Stacks tool. No chapter or unit record is changed. No SGA source, Lean edit, compiler, Lake command, live repository write, or git command was used. Required remote preflight and push follow this report.
