# Q35 stage-1 report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-summable-jump-graph-compactification.json: item, statement unchanged, eight proof steps, status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-real-closed-interval-compact.json: statement, Mathlib leaf, ConditionallyCompleteLinearOrder.isCompact_Icc, Mathlib/Topology/Order/IsLUB.lean:240, specialized to real numbers. Equivalent compact-space formulation compactSpace_Icc at Topology/Order/Compact.lean:114, with instance at line 78.
- citations.json: exact complete statement quotes for each of the eight node citations, indexed by proof step.
- searches.jsonl: actual msearch command records. write_split.py is the sandbox-local reproducible writer; neither is a project node.

## Attachments

None. I searched the live WeilConjectures source for the exact blueprint id and for summable-jump, graph-compactification and two-point-fibre terms; no exact project declaration was found. Broader Topology searches found unrelated constant-subsheaf and stalk files. I have not treated a sorry declaration as a finished proof.

## WANTED

WANTED: a published reference for the summable ordered-jump graph compactification, for lem-sfb-summable-jump-graph-compactification. The latest blueprint's direct-images.proof.md paragraph (3) is the inherited context, not a statement or proof of this topology lemma. The proof is explicitly agent-written. No SGA source is used, no source was downloaded, and no repository or launcher file was written.

## Problems found and corrected

The inherited item was statement-only; there was no earlier sandbox attempt or repair note. Its statement is consistent, and I changed none of its hypotheses or conclusions. Its blueprint ancestor is null throughout the inherited topology branch: tools/blueprint_refs.py ancestor returned null. I preserved this and the via list rather than inventing an ancestor. The latest blueprint is the main-20261023-1620 snapshot identified by COMMITS.txt; I read the latest direct-image proof and unit section rather than the old source snapshot cited by the imported node. The current unit section discusses the six functors and contains no summable-jump construction. This delivery is entirely below that unit, along the already selected countable-cover route.

A potentially incorrect shortcut would apply continuity of the original sum at a jump, or take a pointwise bound as uniform convergence. Step 2 instead invokes the existing uniform-series leaf with its hypotheses verified. Step 3 constructs the genuinely continuous deleted-term sum on A union {v_k}; the omitted term is identically zero, so all terms are everywhere defined on that space. Steps 6 and 7 then prove the graph fibres themselves, rather than cite a new node restating those clauses. I avoided adding sequential-closure and connected-image nodes: the metric-ball choice and pullback-of-separations arguments are written out in the item.

## Unfinished work

No required stage-1 argument is omitted. The only new node is an exact Mathlib leaf, with empty proof, empty proof dependencies and null proof origin. Formal Lean construction is outside this task. An independent maintainer review remains required after delivery.

## Not duplicates

lem-sfb-real-closed-interval-compact vs lem-weil-pbc-closed-in-quasi-compact: the latter requires an already compact ambient space; it does not assert compactness of a bounded interval in the noncompact real line.

lem-sfb-real-closed-interval-compact vs lem-weil-pbc-tychonoff-product-quasi-compact: the latter proves compactness of products from compactness of factors; it does not establish compactness of the real interval factor.

I searched all DAG titles and statements for real interval compactness, compactSpace_Icc and isCompact_Icc, and the full imported blueprint with blueprint_refs.py search 'closed interval'. No duplicate was found. There is no claimed Stacks tag for real-interval compactness; the new node gives the exact Mathlib declaration and source lines. Other blueprint searches ('summable', 'graph closure', 'compact product', 'sequence closure') also found no matching blueprint statement. Existing geometric-series, dominated-function-series, compact-image, Hausdorff-closedness and closed-subset/product compactness leaves were reused rather than duplicated.

## Review by Q35

I read coord/delivery-errors.md B–E in full, the stage-1 brief, the stage document, the three levels in SETUP.md, GOAL.md, worker role, the chapter and unit records, the parent countable-split-cover statement and proof, and the latest blueprint direct-image proof and unit section. This is the elementary topology construction selected by the already reviewed parent, with no change to the unit route. I read the complete statements of all seven existing cited nodes, and the exact Mathlib declaration for the one new node. Every citation in citations.json copies a verbatim statement, not a proof sentence or a source tag.

Step 1 uses only lem-wf-real-geometric-summability for existence of the geometric sum at ratio 1/2. The finite geometric identity and tail estimates are displayed; their limits give the actual sum 1/4, so the cited lemma is not misrepresented as giving that value. At each defined point the absolute-value sequence is exactly the numerical majorant (or that majorant with one index omitted), establishing absolute convergence without a separate dominated-series theorem. The metric completeness used later is the ordinary completeness of the real numbers.

Step 2 uses lem-wf-dominated-continuous-function-series for uniform convergence and continuity, exactly both clauses of its statement. Its complete valued field is R, its topological space and subset are both the subspace A, and the summable majorant is a_j from Step 1. Injectivity ensures c(x) differs from every c(v_j) on A, so the sign terms really are locally constant. Corestriction to the closed interval uses the subspace topology and the already proved bound.

Step 3 applies that same cited statement on B_k=A union {v_k}, with the k-th function zero. For j different from k the point v_j is absent from B_k and c(v_j) differs from c(v_k); hence there is no undefined term or unverified continuity at v_k. The sum at v_k is exactly g_k. Subtracting the k-th term is justified by the finite-sum equality and passing to convergent limits. This supplies both side limits for every sequence in the hypotheses.

Step 4 uses the new exact real-interval Mathlib leaf, lem-weil-pbc-tychonoff-product-quasi-compact for the two compact factors (a product indexed by a two-element set is the usual binary product), and lem-weil-pbc-closed-in-quasi-compact for the graph closure. Their statements require no separation or nonemptiness assumptions. Nonemptiness follows separately from dense A in nonempty V. The displayed maximum metric has product balls; its restriction gives precisely the subspace topology on T. Thus Hausdorffness and metrizability do not depend on any unquoted compactification theorem. Graph density in its closure follows directly by restricting neighbourhoods.

Step 5 uses lem-weil-pbc-continuous-image-quasi-compact with compact T and continuous q from Step 4; its conclusion is exactly compactness of q(T). It then uses lem-sfb-compact-subset-hausdorff-closed, whose ambient Hausdorff hypothesis is V. Closure of the image together with dense A inside it proves surjectivity. These are generic Mathlib tools from other units where applicable; no additional off-route unsplit theorem is invoked.

Steps 6–8 are explicit elementary arguments with no node citations. For Step 6 I checked that closure in the compatible product metric really provides a graph point in every 1/(n+1) ball, and convergence to a point of A is also convergence in its subspace. The height limit is unique in R. Step 7 uses an infinite side subsequence, retaining both coordinate limits; existence of each endpoint uses the given side sequences. A limit of real heights in the closed interval remains there, so there is no circular assertion of convergence inside a subtype to a point not yet shown to belong. Positivity of a_k gives two distinct points, not a possible double label for one point. Step 8 proves connected-image preservation by pulling back a separation. The finite fibre is discrete by disjoint metric balls, so a connected subset in it cannot have two elements. This proves the definition of total disconnectedness actually used by the statement, without confusing it with zero dimensionality.

For small cases I checked k=0 (a_0=1/8, total sum 1/4, gap 1/4), N=0 (tail 1/4), empty connected subsets, singleton fibres, and the two-point separation. An empty A is ruled out by its density in nonempty V. An isolated v_k or an endpoint of the ordered image cannot satisfy the required two side-approximation sequences; neither is silently used as an allowable jump. No density of D is needed or assumed. Removing the two-sided approximation would destroy the assertion that both jump endpoints occur, so the proof explicitly uses it only for that inclusion. No step is over 2000 characters (the longest is 809); there is no hidden identification or separate lemma in a long step.

The required real Mathlib searches ran through msearch.py and their actual results are logged. Natural-language search located continuous_tsum and uniform-convergence declarations; I opened FunctionSeries.lean:33–130 and reused the existing leaf. Sequential closure searches found mem_closure_iff_seq_limit, but a three-line metric-ball proof makes a new node unnecessary. The interval searches found the exact general order theorem, read at IsLUB.lean:240 and Compact.lean:78,114; its real-order instances introduce no hypothesis beyond R. Searching the entire item in a second phrasing returned extension/closure facts and LinearPMap's linear-graph theorem, none of which asserts the nonlinear jump compactification. The item therefore requires this split and is not itself a Mathlib leaf.

The first server dry run rejected the new interval leaf because its statement had no node citation. I added the same universe convention as the item, explicitly citing def-weil-size-convention in its statement and stmt_deps, and read that convention. This changes no mathematics of the real interval; it records which containing universe holds its subspace and covers. Regenerated citations.json so Step 4 quotes the updated statement exactly.
