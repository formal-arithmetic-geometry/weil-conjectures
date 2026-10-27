## Worker report

Files written: dag/nodes/sec-trace-formula/lem-trf-lft-finite-relative-affine-atlas.json (statement, split using existing nodes only), citations.json, and this report. The item statement is unchanged. There are 0 new nodes and 0 new Mathlib leaves. All four steps are below 2000 characters; their total text is below 3000 characters.

Attachments: none. Searches in lean/WeilConjectures for the exact blueprint tag, relative_affine/relativeAffine and finite affine covering terminology found component constructions, including RelativeGluingPresentation, but no project declaration giving this nested atlas with every stated hypothesis and conclusion.

WANTED: none.

The imported item had no proof. Its statement is true, including quasi-compactness of g_0, without any additional finite-presentation, Noetherian, separatedness, or nonemptiness hypothesis. The source's finite-cover choices have now been expanded. The current literature/blueprint/latest snapshot (main-20261023-1620, 7284bb09daf97437d544c51882b325f9c52cd345) uses the contracting-correspondence proof for lem-trf-local-term-locality; the item's blueprint provenance is historical. This delivery does not change that unit or revive a replaced geometric route: it proves the existing generic 0C4W chart lemma below its already recorded ancestor chain.

Nothing remains unfinished in this split.

## Searches and reuse

Read the item, chapter sec-trace-formula and unit sk-i-curve-zero, and the latest blueprint's chapter/unit and locality proof. Searched the whole DAG by titles/concepts (affine basis, finite affine covers, qcqs permanence, locally finite type affine pairs), and blueprint_refs.py with 'affine cover', 'relative affine', '01IT' and '01T2'; the latter two had no imported blueprint-node matches. The ancestor command returned lem-trf-local-term-locality. Reused lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-affine-opens-basis and the existing definition nodes. Also opened lem-pqf-finite-affine-cover-qc-open, lem-weil-pbc-qcqs-finite-affine-open-cover, lem-weil-pbc-quasi-compact-morphism-preimage-qc-open and lem-weil-pbc-lft-affine-pairs: those stronger/general component statements are unnecessary because the defining finite-type covers already have the desired ring maps.

Ran msearch.py under Q159 and this item with leanfinder (two phrasings), loogle, grep and leansearch. All services responded. Read finiteType_appLE/LocallyOfFiniteType (FiniteType.lean:43-48), quasiCompact_of_compactSpace (QuasiSeparated.lean:255), and isCompact_iff_finite_and_eq_biUnion_affineOpens (QuasiCompact.lean:85). A second semantic phrasing returned affineRefinement and auxiliary affine-limit presentations. These are ingredients rather than a one-line specialization giving the complete two-level atlas over base opens. Actual query texts and results are in searches.jsonl and appended to the item's mathlib_searches; inherited searches and their unavailable verdict are preserved.

## Not duplicates

No new nodes. In particular, no duplicate affine-basis, finite-subcover, lft-affine-pair or qcqs-permanence node was created.

## Review by Q159

I read Stacks limits.tex, Situation situation-descent-property and Lemma lemma-descend-unramified (Tag 0C4W), especially its first proof paragraph. It chooses precisely a finite affine cover of the target subordinate to affine base opens and a finite affine cover of each inverse image. I also read Schemes lemma-basis-affine-opens (01IT), lemma-quasi-compact-permanence (03GI), definition-quasi-compact and lemma-quasi-compact-affine (01K3/01K4), and Morphisms definition-finite-type and lemma-locally-finite-type-characterize (01T1/01T2). The latter confirms the expected chart finite-generation statement. There are no new-node sources to verify.

Step 1 uses exactly clause (1) of lem-weil-pbc-qcqs-morphism-permanence, whose statement I opened: source quasi-compact and target quasi-separated imply the morphism quasi-compact. Here these are U_0 and V_0. It does not require u_0 or v_0 to be finite type or quasi-compact. The source proof is 03GI applied after the structure morphism to Spec Z.

Step 2 uses exactly the point-in-open affine-neighbourhood assertion of lem-weil-pbc-affine-opens-basis twice, first in S_0 and then inside the open v_0^{-1}(W_y) of V_0. It uses the finite-subcover condition verbatim in def-weil-pbc-quasi-compact-scheme only after an actual covering of V_0 has been constructed. Thus no quasi-compactness of the inverse images under v_0 is needed. I deliberately avoided treating the intersection of affine opens as affine or assuming a prescribed affine cover is finite.

Step 3 uses the statement of def-weil-finite-type-morphism, not a hidden theorem in its proof: for each affine target open, local finite type supplies an affine cover with finitely generated coordinate algebras, and quasi-compactness supplies a finite subcover. The quasi-compactness established in step 1 applies to exactly g_0^{-1}(Y_{j,0}) because Y_{j,0} is affine. This is an elementary direct application of the two definitions, marked elementary true. Selecting a subfamily preserves its ring maps; no theorem about arbitrary affine source opens is being assumed. Opens of an open subscheme remain opens of U_0.

Step 4 uses the explicitly stated uniqueness and contravariant functoriality in def-weil-affine-spectrum. The equality v_0 g_0 = u_0 restricted to X_{jk,0} makes the composite R_0^{(j)} -> B_{j,0} -> C_{jk,0} equal to the structural map from R_0^{(j)}. This is exactly the algebra-map compatibility; finite generation has already been obtained in step 3. This step is elementary and makes no additional finite-type assertion about the structure maps to S_0.

For B1--B9, there are no new nodes or hidden subsidiary statements. The item is self-contained, with all schemes, maps, indices and rings introduced, and preserves all definition references. TeX is singly escaped in the decoded strings. C1--C4 were checked by opening every cited statement; citations.json contains a verbatim quote for every uses occurrence. No citation relies on a proof instead of its statement. All cited dependencies are existing definition nodes or Mathlib leaves, so no off-unit unresolved tool lemma or cycle is introduced. D1/D2 are avoided by keeping the chart choices and compatibility argument in the item; no clause was moved into a new node. No proof step exceeds 2000 characters.

For E, I checked the empty target case (then U_0 is empty since g_0 exists, and m=0 works), the empty source case (n_j=0 works for every j), the zero-ring affine charts, and identity/affine morphisms. If S_0 is empty then both other schemes are empty, already covered by m=0. Affine coordinate rings need not be nonzero, integral, Noetherian, or finite over R_0^{(j)}. Quasi-separatedness is used only for the target in step 1; the stronger supplied hypotheses are harmless and have not been silently replaced. No statement dispute or mathematical correction was necessary. The main refinement during checking was to use the defining finite-type cover directly in step 3 rather than add redundant affine-pair or finite-cover nodes.

Validation: first server dry run passed preflight at ce821da0be4. A final source-label cross-check corrected the label beside Tag 01I1 to lemma-morphism-into-affine (the mathematical argument and citations are unchanged); rerunning the server dry run on that correction before delivery.
