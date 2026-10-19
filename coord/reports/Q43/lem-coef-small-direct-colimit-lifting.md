# Worker report: lem-coef-small-direct-colimit-lifting

## Files written

- `dag/nodes/sec-six-functors/lem-coef-small-direct-colimit-lifting.json`: item, statement unchanged, six-step split; Mathlib searches find no exact match or one-line specialization.
- `citations.json`: one verbatim statement quotation for every node cited by every proof step.
- `report.md`: this report. `searches.jsonl` was produced by the required msearch command.

No new nodes and no new Mathlib leaves.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint tag, latching/Reedy/direct-category vocabulary and colimit/lifting vocabulary. There is no project declaration stating this arbitrary-small direct-category theorem. Module filtered-colimit element-lifting declarations do not state it. No Lean was written and no compiler, Lake or build tool was run.

## WANTED

WANTED: Mark Hovey, *Model Categories*, Definitions 5.1.1–5.1.2, Proposition 5.1.4 and Corollary 5.1.5, printed pp. 120–122, for lem-coef-small-direct-colimit-lifting. URL: https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf . An existing Q27 review PDF and its extract were available read-only at `/home/ubuntu/weil-launcher-nt/reviews/Q27__lem-coef-reedy-model-structure__7a95aa1d1c15/`; I read those actual source contents. This is not an archive under the project's literature directory, so proof_origin.by remains agent, with the current blueprint context recorded. No document was downloaded or added to the shared repository.

## Faults and corrections

The shared working checkout lacked the assigned node. The current read-only live-DAG mirror `/home/ubuntu/weil-nt-live-dag/nodes/sec-six-functors/lem-coef-small-direct-colimit-lifting.json` contains it, as does the earlier Q27 immutable review snapshot. I used the mirror's node as the starting copy; the delivery tool will resolve it against its freshly fetched origin base. The shared checkout's Reedy node is also unsplit and stale, whereas the mirror has the Q27 split citing this item. I changed no coordination data and ran no git command myself.

There is no statement dispute: the given natural-number degree permits infinite objects, infinite morphisms, and unbounded degrees. Hovey uses a general ordinal degree; the proof specializes to ordinary induction and recursion here. Its model-category assumptions enter the lifting proof only to supply the assumed relative latching lifting property. Our statement already assumes that property against each fixed p in T, so no model structure, functorial factorization, finiteness, smallness of T, or uniform bound on degrees is introduced.

The shared `lem-coef-direct-wfs-extension` has a finite index and assumes a functorial WFS. It cannot supply the arbitrary-small theorem here. I did not reuse its proof as a black-box statement, and created no replacement node. All new argument is carried in the item's proof.

## Unfinished work

No mathematical obligation left outside the six steps. The second reader must review the split and deliver; this worker only runs --no-push.

## Blueprint and duplicate search

Read the full `sec-six-functors` chapter record, `sk-prop-sf-biduality-general` unit record and the human's three levels. Read the current `main-20261015` ancestor proof at `sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, especially paragraph 2's derived coefficient adjunction. Historical ancestry and maintainer-owned chapter/unit are preserved. The technical direct-lifting induction supports the Reedy/cosimplicial-frame foundation below this unit; no unit step is replaced and no unit realization fields are due for this auxiliary node.

Ran `tools/blueprint_refs.py search` for `latching`, `direct category`, `left lifting`, and `colimit`. The first three have no blueprint match; the colimit results supply notions and unrelated scheme/sheaf/derived results, not this theorem. Searched the whole DAG for 002F and relative-latching/direct-category terms and read the nearby finite-WFS and lifting-class statements. No same-statement blueprint node was found; same_as stays []. No new node exists, so there are no new/existing same-tag pairs requiring a Not duplicates section.

## Mathlib reading

All new recorded search queries were executed by `/home/ubuntu/weil-launcher-nt/msearch.py Q43 lem-coef-small-direct-colimit-lifting ...`; the exact queries and command-produced summaries are in the node and searches.jsonl. All four services ran successfully. A second semantic phrasing was tried. Earlier search records are retained as inherited records rather than attributed to Q43.

Read pinned `MorphismProperty/LiftingProperty.lean:30–156`: llp's definition, closure declarations and `colimitsOfShape_discrete_le_llp_rlp` (141–144), restricted to Discrete J. Read `SmallObject/TransfiniteCompositionLifting.lean:245–315`: its chain lifting and closure theorem require a supplied continuous well-ordered diagram, not the relative-latching direct diagram in this item. Read `AlgebraicTopology/Reedy/Basic.lean:1–55`: it defines Reedy structures and lists the diagram model structure as TODO. The semantic search's Joyal-trick declaration (`JoyalTrick.lean:36–65`) assumes model classes, factorization and lifting axioms; it does not construct these direct-diagram compatible lifts. The small-object-cardinality declarations (`IsCardinalForSmallObjectArgument.lean:76–120`) assume a specified relative cell complex and express Hom preservation, not our conclusion. The second phrasing's `ObjectProperty/Local.lean:35–110` colocal theorem requires bijective extensions for objects, rather than existential square fillers for morphisms; `Presentable/OrthogonalReflection.lean:265–300` concerns its particular localization successor. Generic created-colimit and preserved-colimit hits describe universal cocones or functors; their returned types do not assert a lifting property. None turns the item into a Mathlib leaf by one specialization; constructing a cellular presentation would itself be a substantive argument. Our direct proof needs only the two existing nodes already in stmt_deps.

## Review by Q43

I read Hovey's actual Definitions 5.1.1–5.1.2, Proposition 5.1.4 proof and Corollary 5.1.5 proof, printed pp. 120–122, in the existing Q27 PDF/extract. The source's successor step forms exactly the relative latching lifting square, and its final step uses the universal colimit cocone. I also read `literature/stacks-project/categories.tex:1283–1331`, label `definition-colimit`, tag 002F. That tag supplies only the meaning and uniqueness of colimits; I have not cited it as a model or Reedy lifting theorem. No forbidden SGA source appears.

For Step 1 I opened `def-weil-pbc-category-colimit` and `lem-coef-lifting-class-closure`. The former states existence and uniqueness of the map associated to a compatible family; the latter explicitly states both triangle equations for a filler and the definition of the left orthogonal. Those statements justify the reduction to a fixed p and the component square, with no use of the closure node's proof.

For Step 2 the only cited statement is the colimit definition, applied to the nonidentity incoming slice. Every domain has strictly smaller degree; a triangle between two incoming arrows has both domains in the already constructed full subcategory. This verifies the actual cocone, including parallel arrows. Smallness follows from K being small, not from finiteness. The partial-cocone invariant and empty base are written in the step, not imported from an uncited diagram theorem.

For Step 3 the colimit node is sufficient: it also defines pushouts as colimits of spans through the cited lifting-class statement and the item's construction. I checked the equality on each A_j before invoking pushout existence. The two maps agreeing are ell_k L_k f and u_k s_k^A, both from L_k A to X. The relative map has domain P_k and codomain B_k. Thus the proof uses the full relative latching map, not just f_k or the nonrelative latching inclusion. These are explicit universal-property calculations.

For Step 4 I checked both coprojections of the pushout: p u_k = v_k f_k on A_k, and p h_j = v_j = v_k B(alpha) on every B_j. This establishes the lifting square before applying the diagonal property. The cited lifting-class node says precisely that a filler h_k with h_k lambda_k = q_k and p h_k = v_k exists, since lambda_k is assumed in the left orthogonal and p was fixed in T. Restriction along each B_j then yields exactly the new cocone equation. No assertion about factorization, cofibrations or model structures is borrowed.

For Step 5 there is no external mathematical lemma: natural-number recursion and classical choice select fillers already obtained in Step 4. At a fixed degree the objects form a small set, there are no nonidentity arrows within that degree and no arrows to a lower degree. Thus the independent choices impose no mutual compatibility not already checked in Step 4. The step defines the all-degree family and explicitly checks the equation at stage e(k)+1. This elementary bookkeeping does not invoke transfinite-composition closure or a small-object argument.

For Step 6 I again opened the colimit and diagonal statements: the required h is their universal cocone map, and both triangle identities are tested separately on a_k and b_k. Empty K is handled by the uniqueness from each initial object. This is the whole conclusion of the item; it has not been moved into a new node. citations.json contains literal used clauses from the two statements for every occurrence.

For small cases I checked: empty K; a discrete category with arbitrarily many objects of degree zero (independent fillers); a single arrow; two parallel arrows (both are incoming slice objects and both equations are imposed by the latching cocone); a span with arbitrarily many incoming arrows; and a chain with unbounded finite degrees. The proof requires neither finitely many arrows into an object nor an upper bound on the degrees. If T is empty the assertion is vacuous as a lifting class statement. I found no missing hypothesis or false statement to repair. The only correction from the initial plan was resolving the stale shared checkout through the current mirror, rather than treating the absent local file as a mathematical or delivery blocker.

## Second reading by Q43

I reopened the item statement and all six proof steps, the two cited dependency nodes, and the Hovey source passages named in `source`. The statement now explicitly defines the induced map $L_kA\to L_kB$ and the relative latching map $\lambda_k(f)$; its hypotheses and conclusion agree with the arbitrary-small direct-category argument, including the empty category and unbounded natural degrees. The source is Hovey, *Model Categories*, Proposition 5.1.4 and Corollary 5.1.5, printed pp. 121–122; Stacks tag 002F was checked only for the colimit universal property.

- Step 1: checked against `def-weil-pbc-category-colimit` and `lem-coef-lifting-class-closure`; their colimit and diagonal-property clauses justify the component square and reduction to an arbitrary fixed $p\in T$.
- Step 2: checked the nonidentity slice, all commuting triangles, the degree inequality, smallness, the empty base, and the latching colimit universal property; the cited colimit statement says exactly what is used.
- Step 3: checked the induced latching map, both pushout coprojections, the equality on every latching component, and the relative map $\lambda_k(f)$; all cited universal-property uses are stated by the colimit node.
- Step 4: checked the square separately on $A_k$ and on each latching component, then against the exact two triangle equations in `lem-coef-lifting-class-closure`; the resulting restrictions give the required new cocone equations.
- Step 5: checked the natural-number recursion, simultaneous choices at one degree, absence of same-degree nonidentity arrows, and compatibility for identities and incoming arrows; this is elementary bookkeeping from the hypotheses.
- Step 6: checked universal-colimit descent and both triangle identities on every coprojection, including empty $K$ and an object with empty latching category; the cited nodes state the required uniqueness and lifting clauses.
- New nodes: none; therefore there are no new-node statements or Mathlib leaves to inspect. Existing-node searches and the Mathlib searches recorded above were rerun/read, with no exact theorem found.

Changes made during second reading:

- Made the relative latching map construction explicit in the item statement so it is self-contained and no undefined notion is used.
- Added this second-reading record with the source, dependency, hypothesis, edge-case, and citation checks required by the delivery contract.

No statement dispute was found. The existing creation metadata records that this node first entered the DAG with the related Reedy item; the delivery tool preserves that maintainer-owned field.
