# Stage-1 report: lem-sfb-action-clopen-orbit-refinement

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-action-clopen-orbit-refinement.json: split into six steps; retained the mathematical statement and statement dependency; normalized imported doubled TeX backslashes.
- dag/nodes/sec-six-functors-basics/lem-sfb-compact-product-open-neighborhoods.json: statement, Mathlib leaf, exact declaration generalized_tube_lemma (Mathlib/Topology/Compactness/Compact.lean:752–759).
- citations.json: verbatim statement quotations for both proof citations.
- searches.jsonl: actual search-command results, retained without editing.

## Attachments

None. The blueprint tag and concept searches under lean/WeilConjectures found no declaration giving all clauses of the item. The orbit/clopen match in AffineTorsorComponentImageOrbit is about scheme torsor components, and the locally constant cochains docstring match does not state this partition result. The parent's stage-2 declaration is not a completed proof of this item.

## WANTED

None. Bhatt–Scholze and the relevant Stacks source are available locally; the tube lemma is read directly in the installed Mathlib source.

## Corrections and source scope

The original node was unsplit with an empty proof. Its statement is correct: P need only be compact, not Hausdorff or totally disconnected. Only TeX encoding was normalized; no mathematical hypothesis or conclusion changed. No STATEMENT-DISPUTED correction is needed.

Bhatt–Scholze Example 4.1.10, printed p. 28 (read from PDF pages 28–31), identifies pro-objects in finite discrete G-sets with continuous profinite G-sets but does not supply this compact-action partition proof. This split explicitly records an agent expansion, rather than attributing the detailed proof to the paper. It preserves the parent's uniform-preservation / finite-coset-cover / translated-common-refinement route. The chapter and unit records were read; their inherited assignment is unchanged and this is not their key node. The ancestor command returns None for the pre-existing created chain, so the existing ancestor value and via chain are retained; the new leaf extends that via chain by this item.

## Not duplicates

lem-sfb-compact-product-open-neighborhoods vs lem-weil-pbc-closed-in-quasi-compact: the new node gives open product neighborhoods around compact products; the existing node says closed subsets of a quasi-compact space are quasi-compact, and is reused in step 1.
lem-sfb-compact-product-open-neighborhoods vs lem-coef-compact-open-currying: the latter concerns continuity into mapping spaces with the compact-open topology and a locally compact source; the new statement is the separation-free compact-product tube lemma, an exact Mathlib leaf.
lem-sfb-compact-product-open-neighborhoods vs lem-sfb-action-clopen-orbit-refinement: the leaf has no groups, actions, partitions, invariant subgroups or orbit conclusion. It is the generic topological input, not a renamed clause of the item.
lem-sfb-compact-product-open-neighborhoods vs lem-trf-finite-cover-tube-comparison: the latter's tubes are strict-localization fibre products in nearby-cycle comparisons, unrelated to open neighborhoods of compact products.

Whole-DAG searches for tube_lemma, tube lemma, compact slices and product neighborhoods, whole-blueprint searches (clopen; finite clopen partition; tube; tube lemma; compact slice; product neighbourhood; invariant partition), and project Lean searches found no existing statement of the new leaf. The broad DAG searches also found many occurrences of unrelated categorical slices, which were excluded by reading their statements/titles. No Stacks tag is assigned to the new Mathlib theorem: 005C is used only for the existing closed-subset result.

## Mathlib searches

The item's original search records were preserved. New semantic searches used two phrasings of the compact-action partition assertion; no exact match appeared. The returned open-normal-subgroup existence lemmas give an explicit hypothesis already assumed in this item, not the uniform block-preservation theorem. The clopen-cover refinement theorem assumes compact Hausdorff totally disconnected spaces and gives no group invariance. The minimal-action and properly discontinuous-action theorems impose hypotheses absent here. The full-source invariant/clopen/partition regex had no hits.

For the new leaf, LeanFinder and LeanSearch both returned generalized_tube_lemma, Loogle found its exact signature, and the recorded directory grep located it at line 752. I read its docstring, full signature and proof at lines 747–759. It is an exact match for arbitrary topological spaces and arbitrary compact subsets, including empty subsets. The compact subsets carry the induced topology of def-kun-subspace-topology; I read that existing definition and added it as the leaf's statement dependency after the first preflight correctly rejected a citation-free statement. A separate filename-targeted grep hit printed a malformed file field because rg omits the filename for a single input file; that raw log entry is retained, but the node records the earlier directory grep, whose file and line are correct. No service failure was recast as a no-match verdict, and no unrun search was recorded.

## Review by Q22

I checked the item against Bhatt–Scholze Example 4.1.10 as the motivation, the parent's finite-quotient split as the specified route, and Stacks topology.tex Tag 005C, label lemma-closed-in-quasi-compact, lines 1662–1676 for closed-block compactness. For the sole new node I read generalized_tube_lemma directly at Mathlib/Topology/Compactness/Compact.lean:752–759. Its hypotheses require only compact subsets and an open containing set; this matters because P in our item is not assumed Hausdorff.

Step 1 cites exactly the closed-subset compactness statement. Its hypotheses hold because every partition block is closed and P is compact. The empty case is separated before selecting blocks or taking products of block choices: the orbit is the singleton containing the empty partition, and its common refinement is empty.

Step 2 cites exactly the new compact-product neighborhood statement with X=G, Y=P, K={1}, L=A, W=a^{-1}(A). The previous step gives compact A; the singleton compactness argument is included, continuity gives the required open inverse image, and the identity law gives its containment of {1}×A. Dropping the second neighborhood supplied by the tube lemma immediately gives U_A A⊆A. Neither cited node is used for material merely occurring in its proof. citations.json quotes their entire statements verbatim.

Step 3 uses only the explicit open-normal-subgroup basis hypothesis, finite intersection of open neighborhoods, and the inverse element in a subgroup. I checked both inclusions nA⊆A and A⊆nA: the latter follows from n^{-1}A⊆A, not from an unjustified compactness argument. This proves blockwise equality, stronger than setwise preservation of the partition.

Step 4 writes out the finite-orbit argument rather than silently citing finite index: each coset is open by the continuous inverse translation, compactness of G selects finitely many covering cosets, and g=g_i n implies gα=g_iα by the equality already proved. No general quotient discreteness or finite-index theorem is hidden here. Normality is available as required by the conclusion, although this orbit argument needs only that N is a subgroup.

Step 5 checks every partition clause directly. Fixed group elements act by continuous inverse maps, so translated blocks are nonempty clopen and form partitions. The finite set of choices gives finitely many intersections; finite intersections preserve clopenness. A point selects a unique block in each partition, and different choices differ in a disjoint coordinate. These observations give cover and disjointness after empty intersections are discarded. The identity translate is in the orbit, giving refinement of α.

Step 6 checks equivariance with its actual formula: multiplication by h permutes the orbit partitions, and h sends an intersection of chosen blocks to the intersection of their images, reindexed by that permutation. The inverse h^{-1} proves surjectivity on the refined blocks, and bijectivity on P preserves nonemptiness. This proves the exact G-permutation assertion without adding any continuity claim about the finite action that this item does not state.

I tested trivial G, the one-block partition, finite discrete P, empty P, and compact non-Hausdorff P. A finite partition of an indiscrete nonempty P has only its whole-space block and is covered by the argument. For the new tube leaf, empty K or L causes no failure and separation is not needed. No new unsplit node or restated clause was introduced. Steps 3–6 are explicit short arguments from the hypotheses and definitions; the non-elementary compactness input in steps 1–2 is cited. Every step is below 600 characters, so no long step conceals a separate lemma. No circular parent citation was introduced, and both proof dependencies are leaves. The new leaf's statement dependency def-kun-subspace-topology is also a Mathlib leaf and defines exactly the relative topology used in its compactness convention. No off-route unresolved theorem is used.

## Unfinished work

None in this stage-1 item. No Lean was written or compiler/build tool run. Delivery checks and push are performed with the prescribed launcher tool.
