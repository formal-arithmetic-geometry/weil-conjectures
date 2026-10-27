## Worker report

Files written: dag/nodes/sec-trace-formula/lem-trf-relative-global-ci-ring-colimit-descent.json (statement; split, not a Mathlib leaf), citations.json (11 verbatim cited-statement records), report.md. searches.jsonl records the five actual searches from this attempt. prepare.py is sandbox-only preparation.

## New nodes

None. There are 0 new nodes and 0 new Mathlib leaves. The source's three substantial tools were already in the DAG.

## Attachments

None for the item. Searching lean/WeilConjectures for the exact blueprint tag and for complete-intersection colimit descent gave no declaration proving it. The existing RingHom.exists_finitePresentation_model_stage is a general comparison-isomorphism tool, not the assigned complete-intersection conclusion. Its source is lean/WeilConjectures/RingTheory/FinitePresentationModelStage.lean, theorem at line 49; its proof has no sorry. I do not infer transitive closure from this textual observation or report it as an attachment.

## WANTED

None. All sources used are in literature/stacks-project/algebra.tex.

## Findings and changes

The item was unsplit, with no sandbox predecessor or repair order. Its statement agrees with Stacks 0C33, lemma-colimit-lci, the relative-global-complete-intersection case. The only extra conclusion, persistence at all later stages, follows from 00SS (1). I did not alter the statement, hypotheses, chapter, unit, ancestry or historical searches. The source does not require B_0 or C_0 to be finitely presented over the starting base; the model-stage dependency also explicitly requires only finite presentation of the map B_0 -> C_0.

Read the current latest blueprint's chapter, sk-i-curve-zero, and lem-trf-local-term-locality statement/proof. The nodal/alteration ancestry in the assigned item's metadata is historical: the current local-term proof uses the contracting-correspondence theorem. This split makes no assertion that the auxiliary occurs in that current text and does not change the chapter or unit. The exact mathematical route for the assigned item is its recorded Stacks 0C33 paragraph.

The generic tools from sec-proper-base-change are declared in split_report.tool_uses for maintainer review: lem-weil-pbc-relative-global-complete-intersection-noetherian-approximation (00SU), lem-weil-pbc-finite-presentation-model-stage (00QO and isomorphism descent packaged together), and lem-weil-pbc-relative-global-complete-intersection-base-change (00SS). These implement exactly the tools named by 0C33 rather than substituting another proof route. No maintainer-owned tool_uses field was written.

## Searches and reuse

Searched the full DAG by 0C33, 00QO, lemma-colimit-isomorphism, lemma-relative-global-complete-intersection-Noetherian, and complete-intersection/colimit, model-stage and comparison-isomorphism concepts. Opened the statements of the candidate nodes, including the weaker comparison-map-finite-stage and the model-stage theorem. Reused the latter because it gives the compatible isomorphism with no flatness restriction on P -> Q. Blueprint searches for complete intersection, complete.*intersection.*colimit, 0C33, 00SU, finite presentation model and Noetherian approximation found no blueprint duplicate of the item or a missing ingredient. Ancestor lookup confirms lem-trf-local-term-locality.

Ran the prescribed msearch.py commands with this group and item: LeanFinder twice with different formulations, Loogle for "CompleteIntersection", grep for CompleteIntersection|[Ss]yntomic|relativeGlobal.*[Cc]olimit in RingTheory, and LeanSearch for complete-intersection presentation descent. All services answered. Their hits were read: categorical ring colimits and finite-presentation factorization/equality, universal polynomial factorizations, quasi-finite and standard-smooth results. Standard smoothness adds a Jacobian condition and cannot prove arbitrary relative global complete intersections. The Mathlib source FinitePresentation.lean and Algebra/Category/Ring/FinitePresentation.lean confirms that the factorization hits do not assert the item. Every new search record copies the actual log entry; the item's inherited Q100 searches are retained as history.

## Not duplicates

No new nodes. In particular, no duplicate of the existing 00SU, 00SS or finite-presentation model-stage node was created, and no clause of this item was moved to a new node.

## Review by Q111

I read algebra.tex Tag 0C33 (lemma-colimit-lci), the first proof paragraph, and verified its assumptions against the entire item: a chosen initial stage, a map of its algebras, finite presentation of that map, and a relative global complete intersection after tensoring to the colimit. I also read 00SP (definition-relative-global-complete-intersection), 00SU (lemma-relative-global-complete-intersection-Noetherian), 00SS (lemma-base-change-relative-global-complete-intersection) (1), 00FP (lemma-Noetherian-finite-type-is-finite-presentation) (3), 00QO (lemma-characterize-finite-presentation) and 0C32 (lemma-colimit-isomorphism), checking their labels in tags/tags where used. There are no new statements requiring a separate source review.

Step 1 cites def-weil-pbc-relative-global-complete-intersection. Its statement includes the existential polynomial quotient and the algebra isomorphism, so it really permits the choice of T and h; it is not merely a presentation-specific predicate. The equality of the structure map with the given map is built into being a B-algebra isomorphism. This is the only elementary step.

Step 2 uses lem-weil-pbc-relative-global-complete-intersection-noetherian-approximation for the same equations over a finite type integer subring P; its statement explicitly contains the coefficients and the complete-intersection assertion about Q. The finite-type/Noetherian finite-presentation node supplies finite presentation of P over Z; the required Noetherian hypothesis on Z is checked by the least-positive-element ideal argument written in the step, including the zero ideal. def-weil-pbc-finitely-presented-algebra supplies finite presentation of the explicit Q. Part (a) of the base-change node, whose statement I opened, supplies the actual B-algebra presentation isomorphism. Composing with h gives the comparison isomorphism with its required left-inclusion equation. No additional condition on the original B_0 is used.

Step 3 cites lem-weil-pbc-finite-presentation-model-stage, whose statement I opened and compared with its upstream Lean signature. It has precisely the fixed B_0,C_0, finitely presented phi_0, the finite presentations of P and Q, and a ring isomorphism with the required composite equation. Its conclusion includes that same equation at the chosen stage. I therefore use its statement, not a construction hidden in its proof. Applying the base-change node parts (a),(b) to Q over P yields the quotient presentation over B_i and its fibre condition. The definition then turns the composed isomorphism into the asserted property of the specified B_i -> C_i map.

Step 4 cites lem-weil-pbc-tensor-cancel-base-change for the nested tensor cancellation; its statement includes the algebra isomorphism and the pure-tensor formula. The first change of tensor base is written explicitly with an inverse: the B_0 factor acts on C_i through the given phi_0, so balancing is valid even when none of the maps is injective or flat. The formula on r tensor b verifies that the final map is 1 tensor phi_0. Parts (a),(b) of the existing 00SS node then supply the base-changed quotient and its complete-intersection condition. The definition supplies invariance through the displayed algebra presentation isomorphism. Thus all non-elementary facts have statement citations and no unidentified transport assertion remains.

For the hypothesis/edge-case audit, I checked a singleton directed system (all assertions reduce to the initial witnessing presentation), empty variable and equation sets (finite presentations and the same maps still make sense), C=0 and the case c>n (the fibre condition is vacuous when all fibres are zero), a zero colimit ring, and noninjective transition maps. The descent tool allows arbitrary ring transitions and zero rings; no argument treats a stage map as an inclusion. Nonemptiness and the selected i_0 make the required tail available. No flatness or finite presentation of the initial algebras over the base is silently added.

Against delivery-errors B through E: no new-node self-containment, duplicate, Mathlib-leaf, tag or definition issues arise; the item's definition references are retained. Citations were copied verbatim from the exact statement field for every step/node pair. The proof assembles strictly more general existing results; it does not relabel its own clauses as dependencies and creates no recursive dependency. Every step is below 2000 characters. I corrected the initially implicit map compatibility by writing the left-inclusion equation in steps 2 and 3 and the balancing/pure-tensor formulas in step 4. No statement dispute or source error was found. The server dry run passed (preflight OK); the final report correction only fixes the referenced theorem line from 48 to 49. The final dry run and push follow.
