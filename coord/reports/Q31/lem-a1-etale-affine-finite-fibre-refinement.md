# Stage-1 report: lem-a1-etale-affine-finite-fibre-refinement

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-etale-affine-finite-fibre-refinement.json: item, statement, split. Statement unchanged; three proof steps, all using existing DAG nodes or elementary set operations.
- citations.json: eight verbatim statement quotations, one for every cited node in every step.
- report.md and searches.jsonl: review and actual Mathlib searches.

There are 0 new nodes and 0 new Mathlib leaves.

## Attachments

None. Searched the project WeilConjectures source for the exact blueprint tag and for finite fibres and affine refinements. Etale.exists_affine_refinement in ConstructibleSheaf/FreeLifting.lean:57 supplies a related sieve refinement but does not assert this item's source-open selection, quasi-finiteness clauses and exact fibre-image equality. ProperQuasiFinite.lean:68 supplies the existing finite-fibre tool, not the full item. No exact complete project declaration was found.

## WANTED

None.

## Findings and Mathlib searches

The source statement is sound and is retained verbatim. Read Stacks descent.tex Tag 03X4, lemma-locally-quasi-finite-etale-local-source, especially its affine finite-fibres paragraph. It treats an affine source. For the arbitrary source in this item, read topologies.tex Tag 0218, lemma-etale-affine: it expressly allows each member of the finite affine refinement to be open affine in an original source. Its proof is omitted; step 1 supplies the argument using affine neighbourhoods, openness, and quasi-compactness of the target. Read morphisms.tex Tags 01TH, 01SH, 01S7, 01TJ, and 02NH for the restriction and finite-fibre part.

Retained the original Q22 source, blueprint provenance and all logged search records embedded in the item. Read their outcomes, including the two previous phrasings. Current searches, recorded by msearch.py, again find only the individual tools. Read Mathlib Morphisms/Affine.lean:58 and :181 and Morphisms/QuasiFinite.lean:174. The latter requires quasi-compactness of the map; it cannot be applied directly to X to Z. The affine refinement of a scheme's own open cover is not the finite image-cover assertion of this item. Searches for the affine-morphism tool found isAffineHom_of_isAffine; the DAG already has lem-weil-pbc-morphism-affine-schemes-affine, so no new node was created. The newly logged item searches are appended with their actual results.

Read the current blueprint latest/blueprint/sec-purity-real-sheaves/sk-lem-wrp-hc2/lem-a1-affine-hc0.md and its proof and the assigned chapter/unit records. This item remains an auxiliary representability lemma in its recorded ancestry; it does not alter the chapter or unit route. Blueprint searches for finite-fibre affine refinement, affine refinement and morphism of affine found no additional blueprint node stating this item. The source-level generic lemmas are reused as tools, with the two non-Mathlib off-unit uses declared in split_report.tool_uses.

## Not duplicates

No new nodes. Existing affine-basis, open-map, affine quasi-compactness, restriction and quasi-finite nodes are cited directly. In particular no second 01SH or 01TJ node was created, and no clause of this item was moved to a fresh node.

## Review by Q31

I checked the proof against Stacks 03X4 and 0218 rather than assuming the arbitrary source was quasi-compact. In step 1, I read the statement of lem-weil-pbc-affine-opens-basis: it gives affine neighbourhoods in every open and hence an affine open cover of X. I read lem-weil-pbc-etale-morphism-open-map: it gives openness of the image of every open, exactly what is needed for q(A), without requiring q to be quasi-compact or separated. I read lem-weil-pbc-affine-scheme-qcqs: its quasi-compactness assertion applies to W because W is affine. Surjectivity gives the image cover, and the definition of quasi-compactness selects finitely many of these images. This is a cover of W by images, not an unjustified finite cover of X.

In step 2 I checked the full statement of lem-weil-pbc-lqf-restriction-to-opens. Apply it to f=h composed with q, source open A_j and target open all of Z; the required image containment is automatic. It asserts the Stacks locally quasi-finite notion used by the item, avoiding a silent identification with Mathlib's weaker class. I read lem-weil-pbc-morphism-affine-schemes-affine and checked both hypotheses: A_j and Z are affine. It gives affineness of this very restricted composite. Clause (3) of lem-weil-pbc-affine-morphism-permanence then gives its quasi-compactness. The statement of pqf-lem-qf-locqf-qc explicitly provides the conjunction-to-quasi-finite implication. Finally, the forward implication of pqf-lem-qf-finitefibres explicitly gives finite fibres of a quasi-finite morphism. None of these citations requires Noetherianity, separation, or quasi-compactness of X. I made the intermediate affine and quasi-compact arguments explicit instead of treating local quasi-finiteness alone as a finite-fibre theorem.

Step 3 has no external geometric input: I checked both inclusions of the asserted set equality. A point w of a fibre lies in one selected image, so a chosen preimage a still lies in the correct composite fibre. Each right-hand set is the image of a finite set already established in step 2. Finiteness of an image and of a finite union is elementary. Thus the proof does not confuse scheme-theoretic fibres with inverse-image sets or infer a factorization merely from a point image.

I tested empty W (choose m=0), empty Z (a map W to Z forces W empty), X an infinite disjoint union of copies of W (only a finite image-cover is selected), and fibres over points not in the image of h (both sides empty). All satisfy the proof as written. No statement correction or dispute is needed. Every cited statement has a verbatim quotation in citations.json, no proof step exceeds 2000 characters, all elementary flags are boolean, and no new statement-only node needs further hypotheses or searches. The final set argument is the only elementary step. I checked delivery-errors B through E: no new-node form issues, no use of a cited proof instead of its statement, no circular invocation of the parent source-locality theorem, and no relabelling of the item's clauses.

## Unfinished work

None in the one-level split. The two existing generic non-Mathlib tools remain their own nodes; this delivery does not modify them.
