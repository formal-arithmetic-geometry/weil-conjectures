## Worker report

Item: lem-sfb-noetherian-dvr-closed-diagonal. Group Q71. Stage 1 only, 2026-10-23.

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-dvr-closed-diagonal.json: existing statement, split; no exact Mathlib match.
- citations.json: nine entries, quoting the statements of all nodes used by the five proof steps verbatim.
- report.md and the required msearch.py-generated searches.jsonl.

New nodes: 0. New Mathlib leaves: 0. The statement and stmt_deps are unchanged. There was no earlier sandbox attempt, report, split, or search log. The live node was unsplit, without a released repair note or a finished declaration attached. No repository or launcher file was written; no git command, compiler, Lake or build was run by this worker.

Attachments: none. Searching WeilConjectures/ for the exact blueprint tag and item id found no declaration. Concept searches for noetherian, DVR, IsDiscreteValuationRing, discrete valuation, separatedness and valuative criteria found coefficient-ring results and the dense-source criterion in Compactification/ValuativeCriterion.lean. That criterion assumes unique lifts for valuation rings and a dominant source, not the DVR uniqueness of this item. The project complement Morphisms/Separated.lean supplies a closed diagonal when separatedness is already assumed. None is an attachment for this item. Sheaf/ declarations containing sorry were not counted as completed proofs.

WANTED: none.

Problems found: the imported node was statement-only. No statement correction or mathematical source error in the item is needed. The existing boundary-DVR node explicitly restricts Stacks 0CM2 to points outside the image; the application here is exactly in that restricted range, so it avoids the unrestricted source's field/trivial-specialization problem. The source 0207 proves the stronger generic-DVR criterion through an irreducible component. Our assumption concerns all DVR squares, so its finite-type diagonal-boundary argument assembles directly with the already existing boundary-selection node; no generic-point refinement is needed. This retains the same diagonal proof route, rather than replacing the geometric rigidity prerequisite.

Unfinished work: none at this level. Existing cited nodes are reused, not re-split.

## Sources and searches

Read Stacks limits.tex, Tag 0207, label lemma-Noetherian-dvr-valuative-separation, especially the finite-type Noetherian paragraph and the two final diagrams; and Tag 0CM2, label lemma-reach-point-closure-Noetherian. Read schemes.tex, Tag 01KJ, lemma-diagonal-immersion, and Tag 01IQ, lemma-immersion-when-closed. Read morphisms.tex, Tags 01T4, lemma-base-change-finite-type, 01T5, lemma-immersion-locally-finite-type, and 01T6, lemma-finite-type-noetherian; and properties.tex, 01OV definition-noetherian, 01OW lemma-locally-Noetherian and 01OZ lemma-Noetherian-topology. Checked tags against literature/stacks-project/tags/tags. Read the item chapter and unit records, SETUP's three levels and tool-lemma rule, and the main-20261015 unit and direct-images proof. The inherited blueprint.from.node is null (also returned by tools/blueprint_refs.py ancestor); its detailed place and via chain are retained.

Whole-DAG searches covered 0207, 01KJ, 01IQ, the boundary-DVR node, finite-type diagonal, immersion finite type, finite-type-over-Noetherian permanence and Noetherian opens. Blueprint searches were run for Noetherian dvr, diagonal, 0207, valuative separation, DVR uniqueness and closed diagonal. None supplies a duplicate of the item. The matching existing general tools are cited directly. In particular no node was created for the fibre-product calculation or for combining locally finite type with quasi-compactness.

The required msearch.py commands were run and their actual output read: LeanFinder for a finite-type Noetherian map with unique DVR lifts, Loogle for AlgebraicGeometry.IsSeparated and AlgebraicGeometry.ValuativeCriterion.Uniqueness, grep for dvr|discrete.*valuation|uniqueness.*[Ss]eparated in AlgebraicGeometry, and LeanSearch for DVR diagrams implying closed diagonal. A second LeanFinder phrasing asked about two trait maps agreeing generically and over the base. All services answered. The hits IsSeparated.of_valuativeCriterion, ValuativeCriterion.Uniqueness and the closed-diagonal equivalences were checked against Mathlib/AlgebraicGeometry/ValuativeCriterion.lean:29,86–87,246–247. They quantify over all valuation rings; they do not imply this item in one line. The second phrasing returned the definition and equivalent characterization of separatedness, not the Noetherian DVR reduction. Prior searches already recorded by the node's creator were retained, and only actual Q71 searches were appended.

## Review by Q71

I read the item against 0207's finite-type diagonal paragraph. Its hypotheses are sufficient: S is both locally Noetherian and quasi-compact, f is locally of finite type and quasi-compact, and uniqueness is tested for every DVR, with no excellence, finite-type condition on the DVR, dominance or generic-image restriction. The conclusion is the actual diagonal into X times_S X being a closed immersion. None of these hypotheses or clauses changed.

Step 1 uses the statement of lem-weil-pbc-finite-type-over-noetherian first for X over S and then for Y over X. It explicitly says a finite-type scheme over a Noetherian scheme is Noetherian. The projection p1 is a base change of f, and lem-sfb-finite-type-composition-base-change clause (2) supplies precisely its finite type, with no assumption on the other map. The statement of lem-weil-pbc-diagonal-immersion says the diagonal of every scheme morphism is an immersion, without assuming separatedness. Thus the first step establishes the correct target Y's Noetherian property and the needed immersion independently of the desired conclusion.

Step 2 uses lem-weil-pbc-immersion-base-change-lft clause (2), which says an immersion is locally of finite type. To check quasi-compactness, it does not assume a morphism from a quasi-compact source is automatically quasi-compact: for each affine target open V, the inverse image is an open of the already Noetherian X, and lem-weil-pbc-noetherian-open-subscheme-noetherian explicitly makes that open Noetherian, including quasi-compactness of its underlying space. This is exactly the condition in def-weil-finite-type-morphism. These three statements together give finite type of the diagonal. They are the 01T5 and Noetherian-topology inputs in 0207, not a new diagonal lemma hidden inline.

Step 3 uses lem-sfb-noetherian-image-boundary-dvr, whose statement I opened in full. It requires a finite-type map to a locally Noetherian target and a point in the closure but outside the image. Steps 1 and 2 give the first two conditions, and the chosen y gives both point conditions. It supplies both maps u and v, their commuting square, a genuine DVR with its fraction field and the closed-point equation. It is not just an abstract existence or closure assertion. The item does not use that node's proof or its stronger generic-component formulation in Stacks.

Step 4 is elementary relative to def-pc-fibre-product, whose statement gives the projections, their equality over S and uniqueness for a pair of maps from every scheme T. I checked the equations: f p1 v=f p2 v; p_i v j=p_i Delta u=u; uniqueness in the item's hypothesis gives h1=h2; v and Delta h1 have both projections h1, so they are equal as scheme morphisms, not merely on points. Evaluating at the closed point places y in the image, contradicting precisely y outside the image. No claim that a set-theoretic image inclusion gives a scheme-theoretic factorization is used.

Step 5 uses the exact statement of lem-weil-pbc-immersion-closed-image-closed-immersion: an immersion is closed if and only if its image is closed. The immersion was proved in step 1 and the image closedness in steps 3–4. The statement agrees with schemes.tex 01IQ; no properness or separatedness is smuggled in.

All nine uses have verbatim quotations in citations.json, and proof_deps is their exact union. Off-unit citations other than the boundary lemma are existing Mathlib leaves and therefore generic tools under the contract; the boundary lemma has the item's own unit. No new tool-use permission or route departure is necessary. Each step is shorter than 2000 characters (the entire proof is 1801 characters), and none moves the item's conclusion into a new node. There are no new statement-only nodes to audit for missing definitions, missing searches or same-tag duplication.

I tested the reasoning with X empty, an affine separated finite-type X, a nonreduced affine scheme and the affine line with doubled origin over a field. The empty image is already closed; nonreduced structure causes no issue because step 4 uses categorical equality. For the doubled-origin line, Spec k[t]_(t) has two maps with the same generic restriction and base map but distinct closed-point images, so the hypothesis correctly fails. These checks also confirm that no unsupported reducedness or irreducibility assumption was introduced. No SGA source is used. The corrections made during preparation were to spell out quasi-compactness via Noetherian inverse-image opens and to state the equality v=Delta h1 by the full fibre-product universal property.

## Not duplicates

No new nodes were created. Existing general results were reused; none was restated as a new clause of the item.
