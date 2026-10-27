# Q11 stage-1 delivery

Item: lem-trf-embedded-to-intrinsic-smooth-resolution. Date: 2026-10-23.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-embedded-to-intrinsic-smooth-resolution.json: existing statement, now split in nine steps; no statement change; no exact Mathlib match.
- citations.json: one verbatim statement quotation for every citation of every step.
- searches.jsonl: actual searches recorded by msearch.py; the item JSON retains the inherited searches and adds the six searches performed during this task.
- report.md: this report. write_split.py is sandbox-only preparation material, not a delivered node.

There are 0 new nodes and 0 new Mathlib leaves. All algebraic and geometric tools were already in the DAG.

## Attachments

No attachment for the item. Searches of lean/WeilConjectures for its blueprint tag, embedded resolution, intrinsic resolution, resolution/ambient, and desingularization found no declaration stating the item. The Popescu declarations concern a different kind of desingularization. The existing Algebra.exists_standardSmooth_quotient_lift belongs to lem-weil-pbc-standard-smooth-quotient-lift; it is already attached there and is used as that node's statement, not claimed as an attachment of this item.

## Wanted documents

None. I read the local ILO PDF and the local Stacks source. The theorem is conditional on the embedded assignment being supplied; this delivery does not claim to prove existence of that assignment or to have read the additional Bierstone--Milman references cited by its definition.

## What was wrong or incomplete

The item was a statement-only task extracted from old Steps 1--3 of the ordinary-resolution parent. Its source correctly says that ILO does not quote this conditional reduction as a separate theorem. I supplied the argument as agent-written, rather than crediting ILO with the whole proof. No statement dispute or alteration of hypotheses was necessary.

Two points required care: the definition supplies intrinsic comparisons and smooth ambient comparisons without an explicit axiom relating the two; their required compatibility follows from rigidity of ordinary blowups, proved in Step 2. Also equality of center supports would not identify the blowup centers: Steps 6--8 use equality of the actual ideal subsheaves.

I read the chapter and unit records and the current latest blueprint locality statement and proof. The present unit uses contracting correspondences, whereas the assigned item retains historical alteration/resolution ancestry. I preserved that ancestry explicitly in split_report.blueprint and did not change the chapter, unit, or their proof route. This item is not the key node of the current unit, so no unit realization record is delivered.

The inherited statement of thm-nagata-blowup-universal-property has an awkward self-reference; its explicit final-object clause is sufficient for the uniqueness used here. I checked the precise, non-self-referential version in the current latest blueprint and Stacks 0806, and read the recorded project source's corresponding uniqueness interface. I did not modify that other node or silently use an unmentioned construction inside its proof.

## Not duplicates

No new nodes. Before settling on this split I searched all DAG statements/titles for ordinary tower rigidity, standard-smooth quotient lifting, ambient comparison, strict transforms, flat blowup base change, smooth composition, gluing, Noetherian opens and affine finite-type restrictions. I used the existing statements. Whole-blueprint searches for embedded resolution, intrinsic, standard smooth, automorphism, schematically dense and flat base change gave no alternative node stating this item; the ordinary blowup and smooth-chart tools found were reused.

## Review by Q11

I read delivery-errors B through E against the actual node, its cited statements, and the sources. There are no statement-only children to audit. The item retains all objects, coherent ideals, nonempty nowhere dense regular centers, ordered labels, empty and regular inputs, arbitrary smooth maps, cartesian levels, extended ideals and exact unit-ideal deletion.

For Step 1 I read ILO VIII 2.1.3(ii), printed p.87, and 2.3.11--2.3.13, pp.93--94, together with the full statement of def-trf-labeled-embedded-resolution. The latter supplies the regularity, finiteness, coherence, stopping convention, intrinsic ideal comparisons and cocycle, conditionally on E. The existing lemma-nagata-strict-transform-ambient-closed explicitly identifies the strict transform with the ordinary blowup in the pulled-back center, as also stated by Stacks 080E, divisors.tex lemma-strict-transform (1), which I read. This proves the tower assertion without appealing to an existence theorem for E.

For Step 2 I read ILO VIII 2.1.1 and Stacks 02OS/0806 in divisors.tex. I opened thm-nagata-blowup-principalizes-center: its statement gives invertibility as an actual ideal on the blowup. I opened thm-nagata-blowup-universal-property: its final-object clause gives uniqueness. I wrote the induction proving uniqueness of center-preserving tower isomorphisms. This is an elementary consequence of those cited interfaces, not a new lemma node and not uniqueness of a bare birational modification. Identity stages pose no problem. The statement uses specified center ideals, so the uniqueness applies to the given comparisons.

For Step 3 I checked the ambient open construction O=P minus (X minus U): X is closed in P, so X minus U is closed in P and U is its scheme-theoretic inverse image. The embedded definition supplies the open comparison since an ambient open immersion is smooth. The actual statements of lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian, lem-weil-pbc-qc-open-immersion-finite-type and lem-weil-pbc-smooth-restrict-open-subschemes supply the Noetherian, quasi-compact, finite-type and smoothness facts needed to keep O inside E's domain. I read Stacks 01T6 and 01OW and checked their tags; 01T0/01T2 give the quasi-compact open finite-type assertion. I corrected the draft to cite the Noetherian-open statement explicitly rather than hiding quasi-compactness of O.

For Step 4 I read morphisms.tex 01V7 (lemma-smooth-locally-standard-smooth) and 01T2 (lemma-locally-finite-type-characterize), and opened both cited DAG statements. They supply affine U,V and a standard smooth algebra C over A; the second applies to the structure morphisms over Q and supplies finite generation of each affine coordinate ring. A finite generating set explicitly gives the polynomial quotient and its closed embedding. Disjoint unions of these affine ambients give the required finite-union case. The argument does not assume that h is separated or has constant relative dimension.

For Step 5 I read the lifted-equation/Jacobian paragraph of smoothing.tex 07CK and the full statement and current project declaration of lem-weil-pbc-standard-smooth-quotient-lift. It applies to an arbitrary ideal I, not just a nilpotent ideal; this matters because R to A is an arbitrary affine embedding quotient. I read lem-weil-pbc-standard-smooth-is-smooth, lem-weil-pbc-smooth-ring-map-iff-smooth-affine and lem-trf-smooth-composition, and the Stacks 00T7, 01V6 and 01VA interfaces. They justify smooth Q to P and smooth Q over Q. Finite presentation of B over polynomial R gives finite type over Q; affine schemes are separated. The square V=Spec(B/IB)=U times_P Q is cartesian scheme-theoretically, not merely a containment of supports. No lifting of a map by an inappropriate formal-smoothness theorem is used.

For Step 6 I reread the smooth-comparison sentence in the embedded definition. It says cartesian at every cut, pulls back center ideals, and deletes exactly empty centers. Thus the transfer along the isomorphisms constructed in Steps 1 and 3 gives all the data asserted locally. Independence is deferred until the actual ideals have been identified; it is not assumed from the absence of an explicit compatibility axiom.

For Step 7 I checked the finite induction, its initial identification and its hypothesis on preceding levels. The cover is the inverse image of the V opens on the current level over Y. Restriction to these opens is already supplied by Step 3; no affine-intersection assertion is made. At a given label Step 6 gives equality of ideal subsheaves under the preceding identification; Step 2 makes that identification unambiguous. Local membership and the sheaf axiom imply global equality. Unit ideals are likewise detected locally. This routine induction proves the needed ideal equality and removes extra labels; it is not outsourced to a child restating the item.

For Step 8 I read ILO VIII 2.1.9 and Stacks 0805 and 01VF. I opened lem-pc-proper-base-change and use only its smooth clause (2) to make the current projection smooth, then use sbc-lem-smooth-criterion only for smooth implies flat. I opened thm-nagata-blowup-flat-base-change and its statement dependency def-nagata-blowup-flat-base-change-map: together they give the specified comparison and its isomorphism for a flat map. I corrected the draft to make this smooth base-change hypothesis explicit. The unit-ideal case is the explicit Rees algebra O[t], giving an identity stage. This gives the next cartesian identification and completes the induction.

For Step 9 the uniqueness proved in Step 2 applies after the two cartesian pullbacks have been identified. It identifies the global comparison with every local chart comparison and with an embedded smooth comparison when one exists. The same argument proves identity and composition compatibility. Hence arbitrary choices of presentations or lifts have no effect. No non-elementary gluing theorem is hidden here: the next level was constructed by the specified global blowup and its flat comparison, and equality of center subsheaves was checked on a cover, so no descent of new schemes is required.

All 20 step citations have a full verbatim statement quote in citations.json (18 distinct nodes); I checked that each quoted statement supplies the fact described above, rather than mining a cited proof for extra conclusions. Generic tools from other units are declared only under split_report.tool_uses for the maintainer's review. No new nodes, Mathlib leaves, off-route replacement of the resolution input, or SGA citations occur.

Edge cases checked: empty X or Y (empty tower and unit ideal on the empty scheme), regular input (zero length from E), empty equation lists in standard-smooth presentations, nonnilpotent quotient ideals, non-surjective h deleting some or all centers, disconnected charts of differing dimensions, and identity stages needed to compare cuts. For a center that becomes empty only on an individual chart, its label stays in the uncontracted global indexing; only a globally unit ideal is deleted. Small open charts are used rather than claiming an affine overlap. The longest step is below 2000 characters and none hides a separate comparison theorem.

Mathlib searches were run only through msearch.py. I read all returned hits: smooth chart existence and composition were already available through existing DAG tools; manifold smooth embeddings and bordism are unrelated. The two resolution grep phrasings and Loogle blowup search returned no hit. I read the relevant Mathlib Smooth source to check the chart candidates. None states this conditional resolution theorem. No service failure was recorded as absence.

## Unfinished work

None in this stage-1 item. The dependencies already in the DAG remain their own independent tasks. The server review_split check passed and check_dag reported no finding introduced by the sandbox before the final full delivery dry run.
