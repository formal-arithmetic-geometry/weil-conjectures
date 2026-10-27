## Worker report

Q22 split lem-sfb-space-component-generic-chart-dimension, stage 1, 2026-10-24.

Files delivered:
- dag/nodes/sec-six-functors-basics/lem-sfb-space-component-generic-chart-dimension.json: the unchanged statement now has seven proof steps, an exact dependency union, sources, actual Mathlib searches and the split report.
- citations.json: 30 verbatim statement quotations, one for each step/cited-node pair.
- report.md: this report and signed self-review.

## New nodes

None. Zero Mathlib leaves. A proposed dense-open algebraic-space lemma was removed on self-review because its argument is short from existing cited nodes; the argument is explicitly in step 4. There are no statement-only auxiliary files in the delivery.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and algebraic-space/component-dimension notions. No finished declaration states this item. In particular AlgebraicGeometry.topologicalKrullDim_le_of_dense at WeilConjectures/AlgebraicGeometry/DenseCompactification.lean:71 is a theorem about schemes, not algebraic spaces or arbitrary etale charts. Its existing DAG node lem-weil-pbc-dense-open-dimension-comparison is used as a tool, rather than attached to this item.

## Literature and searches

WANTED: none.

Read Stacks decent-spaces.tex, proposition-reasonable-sober (03K6), lemma-dimension-decent-space (0A4J), and their proofs; algebra.tex, lemma-dimension-at-a-point-finite-type-over-field (00OT); varieties.tex, lemma-dimension-locally-algebraic (0A21), especially (3); topology.tex, lemma-image-Noetherian (04Z8). Verified these tag/label correspondences in tags/tags. The item is an agent-formulated consequence, not the verbatim statement of any one tag. The proof is marked agent-written. The scheme dense-open comparison and atlas dimension nodes supply the non-elementary inputs: the proof does not treat the source's prose as a DAG dependency.

Read the chapter and unit records, SETUP's three levels, GOAL, the stage-1 brief and delivery-errors B--E. Read the latest blueprint direct-images statement and proof, especially (3), which delegates the open-direct-image finiteness branch. Retained the item's inherited detailed place and via chain. tools/blueprint_refs.py ancestor reports None: the inherited created.item chain is broken before reaching an imported ancestor. I have not invented an ancestor or changed maintainer-owned provenance. Its existing place explicitly names det-thm-sf-ctf-stability-direct-images (3).

Searched the whole DAG by 0A4J, 03K6, 00OT, 0A21 and dimension/sober/finite-atlas/dense-open/component notions, and read every cited statement in full. Whole-blueprint searches included dimension, generic chart, component dimension, dense open dimension, dense dimension, dense open algebraic space and 0A21; none states this item or a dense-open algebraic-space comparison. Reused the existing nodes for chart dimension, sobriety, finite components, reduced support and dense-open scheme dimension. Kept the original item's searches. Ran five further searches for the item and five for the considered dense-open auxiliary through the required msearch.py command; the precise queries and results are in mathlib_searches and searches.jsonl. LeanSearch and LeanFinder hits were read: genericPoints only supplies generic points once sobriety is known; etale loci/standard-smooth algebra presentations do not prove this dimension comparison. Loogle and Mathlib grep had no hits for the requested combinations. Read Mathlib/Topology/Sober.lean:285--307, Mathlib/Topology/KrullDimension.lean:35--72, the generic-point scheme comparison in FunctionField.lean, and project DenseCompactification.lean:65--90. The subspace inequality from KrullDimension is not dense-open equality.

## Corrections and unfinished work

No statement correction or statement dispute. The imported node had no proof. An attempted auxiliary node would have packaged a three-line dense-open argument; I removed it and wrote that argument in step 4, avoiding an elementary new node. I also checked that local-ring dimension and neighbourhood dimension are never interchanged: at the generic point of affine n-space the former is zero and the latter is n.

No mathematical obligation of the one-level split remains unfinished. Existing cited nodes keep their own stage status. No Lean was written, no compiler or Lake was run, no repository/launcher file was modified, and no agent was started.

## Not duplicates

No new nodes. The entire split uses existing statements. The proposed auxiliary was removed, so none of the shared-source-tag pairs requires a new node.

## Review by Q22

I read the statement against 03K6, 0A4J and 00OT. Quasi-separatedness, rather than separatedness, is sufficient; finite type over an arbitrary field supplies finite-dimensional affine atlases and a Noetherian point space. No smoothness, geometric irreducibility or reducedness enters the argument. A component is nonempty by its definition. The empty space consequently has no components, so its exceptional dimension convention causes no missing case.

Step 1 uses lem-sfb-qc-space-affine-etale-atlas for precisely an affine surjective etale atlas, lem-weil-pbc-affine-scheme-qcqs for its quasi-compactness, lem-pc-affine-finite-type-algebra for its finitely generated coordinate algebra, lem-wf-affine-noetherian-components for its Noetherian topology, and lem-a1-space-point-open-calculus for continuity and surjectivity. Their statements contain these clauses. Chartwise local finite type is an explicit item hypothesis. The descent of stabilization of closed sets is written out using surjectivity, not cited as an unsupported Noetherian descent theorem. This is exactly the elementary argument of 04Z8 following the cited Noetherian chart input.

Step 2 applies lem-sc-noetherian-finite-irreducible-components to the Noetherian space just obtained, not to a space assumed Noetherian without proof. lem-sfb-quasiseparated-space-sober explicitly assumes the same diagonal condition as the item and gives a unique generic point for every nonempty irreducible closed subset. def-weil-irreducible-components gives closedness and maximality. Closure containment proves that the generic point is in no other component, and the finite union of the other components is closed. Thus the resulting open O really is contained in C; no claim that every component is itself open is made.

Step 3 uses the actual existence and pullback clauses of lem-sfb-space-reduced-closed-support; its statement, not merely its proof, identifies the pulled-back point space with p^{-1}(C). lem-trf-space-fibre-products-etale-covers supplies the basechanged etale surjective atlas T -> Z. The affine-quotient clause of def-weil-closed-immersion gives T = Spec(A/I). Images of the generators prove that A/I is finite type, so the assertion that Z is locally finite type is the chart definition, with a concrete finite-type chart. Closedness of C gives quasi-compactness by the cover argument written in the step. The diagonal identification for a subfunctor inclusion follows from the fibre-product universal property and monomorphism; applying lem-sfb-space-quasicompact-affine-tests is justified because it explicitly states quasi-compactness is stable under arbitrary algebraic-space base change. This also proves the needed diagonal property for the open subspaces later used. Reducedness of the pulled-back T is not asserted or needed.

Step 4 is the heart of the proof, checked with both chart-dimension and reduced-support statements open. lem-a1-space-etale-open-image gives exactly the open image J and the surjective etale map N -> J. def-weil-irreducible-components makes its nonempty open image dense in C. The reduced-support pullback clause gives a homeomorphism |Z_J| -> |J| even when J is not reduced. No factorization through the reduced support is inferred from point-image containment (the known delivery error E3). The map T -> Z is open by lem-a1-space-point-open-calculus; this is what proves T_J dense, with the nonempty-open test explicitly written. lem-weil-pbc-dense-open-dimension-comparison assumes a quasi-compact locally finite type SCHEME, and is applied only to the affine finite-type SCHEME T from step 3, with its dense OPEN T_J. It is never applied to an algebraic space, nor does it require T_J to be quasi-compact. lem-trf-space-fibre-products-etale-covers supplies the basechanged atlas of Z_J. lem-sfb-quasiseparated-space-atlas-dimension is used only on the three surjective atlases with quasi-separated targets already verified. lem-weil-pbc-homeomorphism-krull-dimension transports exactly the point-space homeomorphisms supplied by the support statement. These give the written equality chain. There is no hidden comparison lemma left here: only these applications and the one-line density check.

Step 5 uses lem-weil-pbc-dimension-at-point-open-subspace exactly as stated for an open containing w, and then the infimum definition in def-kun-topological-dimension-at-point. All neighbourhoods in that open have dimension dim C by step 4. It does not use the false assertion that an arbitrary dense subset has full Krull dimension, nor that generic-point local-ring dimension computes component dimension. This final infimum computation is marked elementary.

Step 6 uses def-trf-algebraic-space and lem-trf-space-fibre-products-etale-covers for the scheme fibre product and etale projections, and the explicit surjectivity-on-pairs clause of lem-a1-space-point-open-calculus for the point lift. lem-sfb-etale-topological-dimension-at-point states the local TOPOLOGICAL dimension equality for arbitrary scheme etale morphisms with no finiteness, separation or surjectivity restrictions. Thus it applies to both projections even if the specified chart U is very large or not surjective. Step 5 applies to every w above eta, so no residual-field matching assumption is concealed.

Step 7 uses the same atlas comparison on T -> Z and lem-kun-dimension-finite-type on the concrete finite-type scheme T. Nonnegativity follows from the nonempty component and the surjectivity of the atlas: closure of any point gives an irreducible closed subset and hence a chain of length zero in def-kun-topological-krull-dimension. No global bound for every arbitrary chart U is needed.

I tested the statement on Y empty, a zero-dimensional nonreduced finite algebra, an irreducible affine n-space at its generic point, two intersecting components of different dimensions, a reducible nonreduced scheme, and a non-surjective etale chart meeting only the selected component. The open O removes other components without discarding eta, so unequal component dimensions do not contaminate the result. Nonreduced examples explain why Z_J -> J is used as a topological homeomorphism and not an isomorphism. Arbitrary field characteristic has no role in these arguments. There are no new statements to test or definition nodes to add. Every non-elementary step is shorter than 2000 characters. All 30 citation records quote full verbatim statements, which I read for the clauses used as detailed above.

Off-unit tools are declared in split_report.tool_uses with their purpose; these are the standard topology, scheme finite-type geometry, and algebraic-space point/atlas calculus already in the DAG. They do not change the fixed unit route. The main new work is the explicit assembly at the component generic point.
