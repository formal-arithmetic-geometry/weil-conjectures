# Stage-1 delivery: lem-trf-free-map-colimit-split-lifts-tensor-injective

## Files written

- dag/nodes/sec-trace-formula/lem-trf-free-map-colimit-split-lifts-tensor-injective.json: statement, split into four steps; Mathlib verdict: no direct match. The original statement, definition dependencies, source, ancestry and previous search records are retained.
- citations.json: seven step/node entries, with quotations copied verbatim from the cited statements.
- report.md: this report. searches.jsonl was written by the required search command.

No new nodes, hence zero new Mathlib leaves. The proof uses the existing Mathlib leaves lem-weil-pbc-tensor-commutes-with-colimits and lem-weil-pbc-filtered-colimit-modules-elementwise, together with the free-module and tensor-product definition leaves. No unit realization file is needed: this auxiliary item is not the unit's key statement.

## Attachments

None. Searches under lean/WeilConjectures/ for the exact blueprint tag and for split lifts, finite basis spans, tensor/colimit and the relevant free-module notions found no declaration giving the assigned criterion. The additional exact-tag search under lean/Sheaf/ also found none. No Lean was written and no compiler, Lake or build tool was run.

## Literature wanted

None.

## Findings and source audit

I read Stacks flat.tex, Tag 05FQ (lemma-universally-injective-local), in full, particularly its reduction to finite free direct summands and its concluding passage from stage split injections through tensor products to the colimit. I also read Algebra Tags 00D6 (lemma-directed-colimit), 00D7 (lemma-zero-directed-limit), and 00DD (lemma-tensor-products-commute-with-limits). The last displayed target in the prose proof of 05FQ repeats the stage N_i' where the conclusion is the map into N; the assigned statement correctly states the colimit conclusion, and I proved precisely that. No statement correction or dispute is needed.

The latest blueprint files read were sec-trace-formula/sk-i-curve-zero/_section.md and lem-trf-local-term-locality.md / .proof.md. The ancestor now follows contracting correspondences and does not spell out the older semistable-alteration/flattening input recorded in the inherited ancestry. This is reported explicitly in split_report.blueprint: I retain the assigned algebra lemma and its historical ancestry, without claiming the newest proof contains the old sentence or changing the parent, chapter, or unit route. The statement is independently supported by the specified subargument of 05FQ.

## Search and reuse

I read the item's existing search records and retained them. Fresh searches were run through msearch.py, with their exact tool and query text appended to mathlib_searches and logged in searches.jsonl: LeanSearch, Loogle, two differently phrased LeanFinder queries, and two greps. All six calls succeeded. No unavailable service is recorded as a negative result.

I inspected Algebra/Colimit/Module.lean, including Module.DirectLimit.lift_injective (line 157), and LinearAlgebra/TensorProduct/DirectLimit.lean, including directLimitLeft and directLimitRight. lift_injective concerns a map OUT OF a direct limit with injective maps from its stages; our problem concerns a map INTO a direct limit with eventual splittings on finite source spans. The tensor-direct-limit equivalences are useful inputs, already covered by lem-weil-pbc-tensor-commutes-with-colimits, and do not prove the item in one specialization. Other hits, including flatness preservation of injectivity and finite-submodule tensor criteria, require a separate argument or extra hypotheses. The second LeanFinder phrasing returned projective-object and flat-factorization results, not the criterion.

DAG searches by 05FQ, 00DD, 00DA, finite support and tensor/colimit located the existing inputs. I opened their complete node files and statements. Blueprint-wide searches with blueprint_refs.py for 'tensor colimit', 'direct limit', 'universally injective', 'split lifts', and 'finite basis' produced no blueprint statement equal to the item. I checked the hits rather than introducing additional nodes. Consequently no duplicate, elementary-fact node, or node restating a clause of the item is proposed.

## Review by NF

I checked the node files against delivery-errors B through E with Stacks 05FQ, 00D6, 00D7 and 00DD open. There are no new-node sources or statements to audit: the proof is an assembly from existing Mathlib leaves and explicit elementary arguments.

Step 1 uses def-weil-pbc-module-tensor-product for generation by pure tensors and def-weil-pbc-free-module for unique finite basis expansions. Taking the finite union of the supports of the finitely many second tensor factors gives actual preimages in P_E; the displayed sum constructs y rather than assuming tensor preserves an arbitrary injection. This is an elementary consequence of the two definitions. Scalar coefficients can be absorbed into the first tensor factor by bilinearity. The empty sum uses E empty and y zero.

Step 2 uses exactly the colimit-with-its-specified-coprojections conclusion of lem-weil-pbc-tensor-commutes-with-colimits. Its statement puts the fixed tensor factor on the right. I did not silently use the opposite convention: the step constructs the flip and its inverse from the tensor universal property, checks the two composites on the generating pure tensors, and writes the transition/coprojection calculation. Thus it supplies the precise colimit cocone needed in step 3. The index category is small by hypothesis, as required by the cited node; this is a genuine colimit of R-modules, not merely a colimit of underlying collections.

Step 3 uses tensor functoriality from def-weil-pbc-module-tensor-product and the explicit zero-detection clause of lem-weil-pbc-filtered-colimit-modules-elementwise. The latter's statement says that a representative mapping to zero becomes zero along some later map, including its directed-set formulation. The modules in this application are L tensor F_i; step 2 supplies their colimit L tensor N. The given small nonempty directed poset is filtered, and neither citation assumes freeness or flatness of the stages. In particular I did not cite the ring-base-change version, which would not cover arbitrary F_i.

Step 4 uses only the stated retraction hypothesis at the particular j found in step 3 and tensor functoriality/identities from the tensor definition node. The equation y=(1 tensor s)(1 tensor t_ij)(1 tensor v)(y)=0 is written out. No compatibility of the s across indices or supports is inferred. Returning x=(1 tensor a_E)(y) proves the kernel is zero; subtracting equal-image elements gives injectivity. This is elementary after the cited facts, not an additional lemma hiding the conclusion.

I checked every cited node's statement, not its proof, and citations.json quotes the precise generation, basis, colimit and zero-detection clauses, with functoriality quoted for steps 3 and 4. Each quote is a literal substring of the current statement, including the existing zero-detection node's literal doubled-backslash formatting. I corrected the tensor-definition quotation for steps 3 and 4 to quote composition/identities rather than just generation.

The edge cases checked were B empty (M=P_E=0), E empty inside an infinite basis, x zero and empty tensor sums, the zero ring, L zero, a singleton index poset, and arbitrary nonflat F_i and L. No nontrivial-ring, finite-rank, finite-presentation, finite-generation-of-L or flatness assumption is used. Dropping the eventual-stage condition would invalidate zero detection followed by a retraction at that later stage; the proof retains exactly that hypothesis. Every step is below 2000 characters and the total proof text is below 3000; the finite-support reduction, flips and left-inverse calculation are explicitly given rather than moved into new nodes.

## Not duplicates

No new nodes were created. The two substantive auxiliary statements already exist and are reused as Mathlib leaves; the other cited nodes are existing definition leaves.

## Unfinished work

None in the mathematical split. Required server dry run and direct delivery follow this report; their tool results determine delivery status.
