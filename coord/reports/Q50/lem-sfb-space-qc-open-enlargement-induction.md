# Stage-1 report: lem-sfb-space-qc-open-enlargement-induction

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-qc-open-enlargement-induction.json: statement; split into six steps, with no statement change. Mathlib verdict: no match.
- citations.json: verbatim statement quotations for all 12 step citations.
- searches.jsonl: actual Mathlib search records. The item retains the matching original records and adds the source-location grep.
- report.md: this report. write_split.py is a sandbox-only writing helper, not a delivery file.

New nodes: 0. New Mathlib leaves: 0. All prerequisites already exist in the DAG.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for distinguished-square, open-enlargement, and algebraic-space terminology. No declaration states this item. Scheme ideal-extension and derived-category distinguished-triangle results do not state it.

## WANTED

None.

## Corrections and provenance

The statement is correct and unchanged. Its empty proof is replaced by the direct argument of Stacks Tag 09IT, spaces-perfect.tex, label lemma-induction-principle-enlarge. The argument uses the actual statements of existing prerequisites, rather than the existing proof of the related Tag 08GP induction node.

The source proof has a typographical error in its base case: it writes W intersect U_{n+1} = W, although U_{n+1} is empty. For nonempty W this equality is false. The previously defined W_p is W union U_p, so the correct equality is W union empty = W. Step 3 uses that equality. This is a source-proof typo, not a disputed item statement and not a change of the unit route.

Read the current blueprint at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and the recorded unit/chapter. The item is a supporting algebraic-space induction input in the existing perfect-open-retract chain, not the unit's key statement. The inherited blueprint.from.node is null: blueprint_refs.py ancestor reports None. Retained that field and the detailed inherited place/via rather than inventing a blueprint ancestor. Searched all blueprint nodes for induction and distinguished square, and searched the whole DAG for 09IT, 08GN and their labels. No blueprint node states this result. The related lem-sfb-space-qcqs-distinguished-square-induction has a property on all qcqs etale objects and requires affine and overlap base cases; it is not this fixed-open property.

Generic off-unit tools are declared in split_report.tool_uses: finite affine covering, etale open images, point/fibre-product calculus, and representable-etale scheme tests. They implement the given filtration proof and do not replace the unit's route.

## Not duplicates

No new nodes. Reused lem-sfb-qcqs-space-splitting-filtration (07ST), lem-sfb-space-change-base-to-integers, lem-weil-pbc-qcqs-finite-affine-open-cover, lem-a1-space-etale-open-image, lem-a1-space-point-open-calculus, lem-trf-space-representable-etale-scheme-tests, lem-sfb-space-reduced-closed-support, lem-sfb-space-qcqs-permanence and lem-sfb-space-quasicompact-affine-tests, together with the existing open-subspace definition. Did not create a node for the elementary reduced-source factorization or for either finite induction.

## Review by Q50

I read Tag 09IT in spaces-perfect.tex, including its whole direct proof, and the adjacent definitions and Tag 08GN, whose proof is omitted. I also read the proof of Tag 08GP to locate the extra overlap observation; Tag 07ST in decent-spaces.tex for the filtration; Tags 03I4 and 04SG in spaces.tex for the change of base; and the relevant open-subspace, etale-image and quasi-compactness passages in spaces-properties.tex and spaces-morphisms.tex. There are no new nodes needing separate source review.

For step 1 I opened the statements of lem-sfb-space-qcqs-permanence, lem-sfb-space-quasicompact-affine-tests and def-a1-space-open-subspace. The first applies directly to W_1 -> X because W_1 is quasi-compact and X is quasi-separated; it does not require assuming W_2 quasi-separated. The second gives arbitrary base change and agreement with scheme quasi-compactness. The definition makes the pullback an open scheme. The monomorphism W_2 -> X identifies the two fibre products. This verifies the additional overlap clause without a concealed finiteness hypothesis on f.

For step 2 I read both cited statements, especially the restriction S = Spec Z in the filtration node. The base-change-to-integers node supplies the equivalence, preservation of atlases and fibre products, and the identical small etale charts, so reducedness, open subspaces and the point topology are unchanged. Quasi-separatedness is absolute in the item. The transported schemes acquire their maps to S through X. This supplies exactly the scheme charts, surjectivity and reduced-complement isomorphisms later used; no conclusion is taken just from a prerequisite's proof.

For step 3 I checked that the finite-affine-cover node assumes only a quasi-compact scheme; V_p satisfies this. The etale-open-image node explicitly gives an open image, its factorization and quasi-compactness. Finite unions are handled by the written finite-subcover argument, not an unrecorded geometric lemma. The descending induction claim is explicitly P(W_0 union U_p); its base is assumption (i). The inner finite-cover construction has B_0 equal to that induction hypothesis and B_m equal to the next open by surjectivity.

For step 4 I read the statements of representable-etale-scheme-tests, etale-open-image, reduced-closed-support and the splitting filtration. They give etale composition/base change, factorization through the image, existence of C_i, and the radical-ideal description of Z_p. The reduction to U_p is an open factorization. The subsequent closed factorization uses reducedness of C_i: a function vanishing at every point lies in the nilradical and hence is zero. Uniqueness through a closed immersion makes the chart factorizations agree. This is a short affine radical-ideal calculation, written out rather than turned into a redundant node or hidden behind Tag 08GN.

For step 5 I read the full point-open-calculus statement: it gives the fibre-product image formula and explicitly says an open with full point image is the whole space. Pullback of the filtration isomorphism identifies V_p x C_i with C_i. Every remaining point is in the ith affine chart image by the definition of B_i. These two facts make the open V_{p,i} x C_i the whole pullback, proving the scheme-theoretic isomorphism over C_i, not just equality of supports. Thus the squares really satisfy the definition in the item. This step only assembles the already obtained isomorphism, open-subspace pullback, and cited point calculus.

For step 6 I checked every hypothesis of (ii): the B_i are quasi-compact opens in X containing W_0, the charts are affine, and steps 4 and 5 prove the distinguished-square condition. The inner induction then proves the descending-induction step. The empty-chart-cover case is explicit. I tested X empty, W_0 empty, W_0 = X, repeated filtration opens, and empty V_p. None requires a separate base case P(empty) unless W_0 itself is empty. No argument assumes separatedness of X or affineness of intersections.

I checked delivery-errors B--E against the completed files: all definitions used by the statement have their original dependencies, every non-elementary input is a cited existing statement, proof_deps is exactly the union of uses, no new node restates a clause, and all citations.json quotations are verbatim. Every step is below 2000 characters; the proof contains no long step hiding an unrecorded comparison lemma. The two steps marked elementary are the explicit reduced-ideal/open-subspace calculations; the induction assembly is also marked elementary.

Mathlib searches were actually run with msearch.py: LeanSearch, Loogle, LeanFinder in two phrasings, and two source greps. I read all returned hits and the source of AlgebraicGeometry.compact_open_induction_on at Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean:241. It is induction on opens of a scheme with affine open-union steps, not on an algebraic space with etale charts and reduced-complement isomorphisms. It therefore cannot attach or make this item a Mathlib leaf. No search was unavailable or invented.

## Unfinished work

None in this stage-1 split. No Lean was written or compiled. The required dry run and direct push are performed after this report is written; their terminal result is the delivery evidence.
