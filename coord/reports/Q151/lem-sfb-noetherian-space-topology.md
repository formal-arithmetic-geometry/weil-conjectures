# Stage 1: lem-sfb-noetherian-space-topology

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-space-topology.json: statement, split; not a Mathlib leaf for algebraic spaces. Four proof steps, all using existing nodes. The statement and its statement dependencies are unchanged. Prior Mathlib searches and creation metadata are retained; four searches run by Q151 are appended.
- citations.json: four verbatim quotations, covering every external node cited by the four steps.
- report.md: this report. searches.jsonl is the unmodified log produced by msearch.py.

There are 0 new nodes and 0 new Mathlib leaves. The proof reuses two existing Mathlib leaves, lem-weil-pbc-affine-scheme-qcqs and lem-weil-pbc-noetherian-scheme-closed-subsets-minimal.

## Attachments

None. Searched lean/WeilConjectures by the blueprint tag, NoetherianSpace/noetherian topology, and AlgebraicSpace/algebraic space. The project declarations found concern schemes and scheme morphisms, not every clause of this algebraic-space assertion. Mathlib's IsNoetherian.noetherianSpace concerns schemes, so it is an input through an existing DAG leaf, not an attachment of this item.

## WANTED

None: all sources used are present locally.

## Findings and scope

The item is correct as stated, including its minimal-member formulation. No statement correction or STATEMENT-DISPUTED is needed. There was no previous sandbox item, proof, report or search log to resume. The live item had no proof. Its existing source and searches were retained.

Read the chapter record sec-six-functors-basics and unit record sk-thm-sf-ctf-stability, the three-level rule in SETUP.md, and the current blueprint under literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/, in particular the direct-images proof (3). This item supplies the Noetherian-induction input for the later coherent devissage; it does not alter the direct-image route. The existing blueprint creation chain has no imported ancestor: tools/blueprint_refs.py ancestor returns None. The inherited null from.node and its detailed from.place/via are retained; no fictitious ancestor is supplied. Searches of the whole imported blueprint for 'Noetherian topology', 'Noetherian algebraic space' and 'Noetherian scheme', together with DAG statement searches and the source-tag search, found no duplicate of the algebraic-space assertion.

The proof uses the affine presentation already furnished by lem-sfb-qc-space-affine-etale-atlas (03H6), rather than introducing a new local-Noetherian topology node that merely repackages this item's content. The transfer of minimal closed subsets is proved in the item itself, not hidden in a new node. This is below the unit route and uses precisely the chart-to-point-space argument of 04ZF, with the inverse-image argument of 04Z8.

Source detail noticed: the last sentence of the local proof of 03H6 calls the finite union of chart components a 'finite surjective morphism'. The construction proves surjective etale, not necessarily finite. For example the affine etale cover D(t) disjoint-union D(t-1) of A^1 over a field is not finite: its summand D(t) has nonclosed image, whereas a finite map is closed. The statement of 03H6 and the existing atlas node correctly assert etale surjective; the split uses exactly those assertions and does not use the erroneous finiteness word. The item's own source 04ZF is unaffected.

## Not duplicates

No new nodes. Reused the existing atlas, point-map calculus, affine quasi-compactness, and Noetherian-scheme minimal-closed-subset nodes. The node with source 04ZF is the item itself; lem-sfb-space-coherent-devissage merely uses it and states a coherent-module result, not this topology assertion.

## Review by Q151

I read coord/delivery-errors.md B--E in full and checked the actual node statements against each use, not just their titles or proofs. I read spaces-properties.tex 04ZF (lemma-Noetherian-topology), 03H6 (lemma-quasi-compact-affine-cover), 03H5 (lemma-characterize-surjective), and 03BX (lemma-topology-points); properties.tex 01OZ (lemma-Noetherian-topology); and topology.tex 04Z8 (lemma-image-Noetherian, its inverse-image proof) and 0051 (definition-noetherian). No new-node source requires review, since no new node is created. I also read the existing Mathlib Noetherian scheme instance at Mathlib/AlgebraicGeometry/Noetherian.lean:318--333 and the NoetherianSpace equivalences in Mathlib/Topology/NoetherianSpace.lean. The alternative semantic phrasing and the logged Loogle/grep queries confirmed that the scheme result does not directly state the algebraic-space result.

For step 1, I opened lem-sfb-qc-space-affine-etale-atlas: its statement gives an affine scheme W and a representable surjective etale h_W to X from quasi-compactness of the atlas point space, with no quasi-separatedness assumption. This is exactly the hypothesis we have. I opened lem-a1-space-point-open-calculus: its statement explicitly equates representable surjectivity with point-map surjectivity and explicitly makes every point map continuous. Those are the only parts used; no fibre-product or open-subspace consequences are imported. Its use is declared as a generic tool in split_report.tool_uses because its unit differs and this unit has no point-map criterion. The quotations in citations.json include both relevant sentences.

For step 2, local Noetherianity of W follows directly from the item's explicit hypothesis on every etale scheme chart; it requires no descent theorem. I opened lem-weil-pbc-affine-scheme-qcqs, whose statement explicitly supplies quasi-compactness of an affine scheme. I use only that clause, not its quasi-separatedness clause. The combination 'locally Noetherian and quasi-compact' is exactly the definition of a Noetherian scheme required by the next cited node. This short assembly is marked elementary, with the non-elementary quasi-compactness fact still cited.

For step 3, I opened lem-weil-pbc-noetherian-scheme-closed-subsets-minimal. Its statement is exactly the existence of a minimal member of any nonempty set of closed subsets of a locally Noetherian quasi-compact scheme. W meets both hypotheses by step 2. Inverse images of closed sets are closed by the continuity established in step 1. The image family of inverse images is nonempty because the given family is nonempty. The minimal member is chosen in that image family and then represented by a member C_0 of the original family. No injectivity assumption on the atlas or closedness of its images is needed.

For step 4, I checked the elementary strict-inclusion argument explicitly: a point of C_0 minus C lifts along the surjective point map, witnessing strict inclusion of inverse images. That contradicts the already chosen minimal inverse image. This is the entire remaining inference, so no uncited Noetherian-image theorem is invoked. In particular neither a definition-only node nor a source tag is being used as a substitute for a lemma. The step has no external citation because it only uses earlier conclusions and set membership.

Edge cases: if X is empty, its only closed subset is empty and the assertion holds. No nonempty-chart hypothesis is imposed; the empty scheme is affine and quasi-compact. A singleton closed family is allowed, as is a family containing the empty subset. No separatedness or quasi-separatedness of X, Noetherianity of S, finite-type hypothesis, finite atlas morphism, or injectivity of point maps is inserted. Surjectivity is essential and is supplied by the cited point-map criterion. Families are sets of closed subsets, so there is no proper-class index issue.

Against B, there is no statement-only node containing a hidden proof and no invented notion; TeX escaping and the tag/label citations were checked. Against C, each of the four external uses has an exact quotation and proof_deps is precisely their union; none of the cited nodes depends on the item. Against D, the proof writes the actual argument rather than moving the conclusion to a child. Against E, I checked chart hypotheses and empty/strict-inclusion cases as described above. All four steps are shorter than 400 characters, so there is no long step hiding an independent lemma. The report records the inherited source typo without changing the correct item statement.

## Unfinished work

None in the requested one-level split. The final server dry run and direct delivery are performed with the mandated delivery command; no Lean is written, no compiler or Lake is run, and no repository or launcher file is edited.
