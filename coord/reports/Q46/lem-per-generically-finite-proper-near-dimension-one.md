# Q46: lem-per-generically-finite-proper-near-dimension-one

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-generically-finite-proper-near-dimension-one.json: statement item, split into five steps; original statement preserved; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-generically-finite-quasifinite-over-dimension-one.json: new statement-only unsplit node, Stacks Tag 0AB6 condition (1); no Mathlib match.
- citations.json: one verbatim statement quotation for every step/node pair.

## Attachments

None. Searches of WeilConjectures/ in the read-only slopmaster2 source for the item id, generically finite terminology, and finite/codimension terminology found no declaration proving the item exactly. The scheme quasi-finiteness API supplies general tools, not this generic-algebraicity/local-dimension theorem. The upstream master source was also searched for the new child's generic finiteness and codimension statement; its sorry declarations are not evidence of completion.

## WANTED

None. All sources used are present locally.

## Audit and corrections

The item was an unsplit statement imported as a child of lem-per-normal-modification-codimension-one, with no Lean audit recording a completed proof. No prior sandbox node, report, citations, or search log existed. I retained the repository's statement, created record, blueprint ancestry, and earlier Mathlib searches, and appended searches made by this worker. There is no statement dispute or hypothesis change.

The source is literature/stacks-project/varieties.tex, Tag 0AB7, label lemma-finite-in-codim-1, condition (1), and its proof (lines 3267–3297). I read the immediately preceding Tag 0AB6, label lemma-quasi-finite-in-codim-1, including its full statement and proof. The proof of 0AB7 takes 0AB6 as its genuine smaller geometric input: the new child concludes pointwise quasi-finiteness under locally finite type, without properness, whereas the item must still use properness twice, for fibre compactness and the final neighbourhood theorem. It is not a rephrasing of the item's conclusion.

Tag 0AB7 cites the older locally Noetherian finite-fibre-neighbourhood theorem through coherent.tex, Tag 02OH. Its statement assumes a locally Noetherian target, which this item does not have. I read more-morphisms.tex, Tag 02UP, label lemma-proper-finite-fibre-finite-in-neighbourhood, lines 12594–12622, and reused lem-trf-proper-finite-fibre-finite-near, which explicitly supplies the same conclusion with no Noetherian hypothesis. Thus the proof closes the source's citation-hypothesis gap without adding a global assumption. No unit or chapter route is changed: this is the prescribed geometric tool inside the existing normal-modification chain.

## Searches

Before creating the child I searched the whole DAG by 0AB6, the varieties label, generic finiteness, and local Noetherian dimension plus quasi-finiteness; I opened the statements of the same-tag nodes below. I ran tools/blueprint_refs.py ancestor on the item, and search for quasi-finite, finite fibre, codimension, dimension one, codim-1, generically finite, and 0AB6. None states the child's full generality. The blueprint ancestor and via chain are preserved and extended by the item for its child. The current main-20261015 Artin–Gabber proof and the unit/chapter records were read as provenance; the existing ancestor place identifies the technical duality/modification chain in the DAG.

All new Mathlib searches ran through msearch.py and are preserved in searches.jsonl, with the complete returned text copied into mathlib_searches. Two LeanFinder phrasings, Loogle, LeanSearch, and grep were used for the child; the item was also searched through all four tools. All services returned responses. Hits were definitions of LocallyQuasiFinite, pointwise QuasiFiniteAt criteria, and the proper-plus-finite-fibre or proper-plus-locally-quasi-finite theorems; none establishes quasi-finiteness from generic algebraicity over a target point of local dimension at most one. I read Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean around its definitions and fibre criteria, and Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean:406, where exists_isFinite_morphismRestrict_of_finite_preimage_singleton requires an already finite fibre. This useful existing tool is already covered by the cited DAG node, so I created no duplicate Mathlib leaf. The additional single-file grep's formatter prints line numbers in its file field; its raw answer is retained honestly, and no leaf or source location is inferred from that formatter output.

## Not duplicates

lem-per-generically-finite-quasifinite-over-dimension-one vs lem-trf-birational-curve-quasifinite: the existing statement concerns integral separated one-dimensional schemes of finite type over a common field and a dominant map inducing a finite function-field extension. The new statement permits arbitrary schemes, non-dominant components, and only a Noetherian local ring at the chosen target point; neither source nor target is assumed a curve over a field. The existing node cites 0AB6 as an ingredient, rather than stating its generality.

lem-per-generically-finite-quasifinite-over-dimension-one vs lem-trf-proper-birational-curve-finite: the existing statement requires integral separated curves over a field, properness and an isomorphism of function fields, and concludes finiteness. The new statement requires only locally finite type, algebraicity at all component generic points, and local Noetherian dimension at most one; it concludes quasi-finiteness only over the specified point. Their shared 0AB6 reference does not make their statements equal.

## Review by Q46

I checked delivery-errors B through E against the node files and the local Stacks sources. For the item I read 0AB7 condition (1); for the new child I read 0AB6 condition (1) and the whole dimension-formula proof. The child introduces its own schemes, map and point, spells out algebraicity, and cites actual definition nodes for finite type, Noetherian rings, dimension, generic points, components, residue fields and quasi-finiteness. It has no proof sketch, no proof steps, and no proof dependencies. No elementary consequence or existing special case was promoted to a child.

Step 1 uses the properness definition and the finite-type definition only to extract locally finite type, then the new 0AB6 node with the same local ring and the same algebraicity hypothesis. I verified that neither dominance, normality, reducedness, nor a locally Noetherian target is required by 0AB6. Step 2 uses def-pc-scheme-fibre for the actual scheme fibre and its homeomorphism onto the inverse-image subspace, and lem-weil-pbc-quasi-finite-at-point-isolated for open singletons. Its locally-finite-type hypothesis was obtained in step 1. Step 3 uses clause (1) of lem-pc-proper-base-change on the residue-field base change, def-weil-affine-spectrum to identify its affine target, and pqf-lem-proper-basic for quasi-compactness over an affine base. The latter node explicitly states the implication used, so no claim that every proper source is absolutely quasi-compact is smuggled in. Step 4 is elementary: apply the precise finite-subcover definition in def-weil-pbc-quasi-compact-scheme to the open singleton cover and use the already specified fibre homeomorphism. Step 5 uses exactly the statement of lem-trf-proper-finite-fibre-finite-near; I opened it and verified that it takes properness and a finite underlying fibre and imposes no Noetherian condition. The entire statements used are copied verbatim into citations.json for each pair.

I checked small cases: an empty fibre has the empty singleton subcover and still satisfies 02UP; dimension zero is explicitly allowed by 0AB6; a finite morphism already has the required conclusion; the identity of any scheme with the prescribed local ring is consistent with both statements. Nonreduced components introduce no extra reducedness hypothesis. The dimension bound is essential: the blow-up of the affine plane at the origin is proper and generically an isomorphism but has a projective-line exceptional fibre and is not finite near that point of local dimension two. Properness is also genuinely used after the child: an infinite disjoint union of copies of a field spectrum is locally finite type with algebraic generic residue extensions and discrete fibre, but that fibre is not compact, so the elementary finite-subcover step cannot be applied without the properness input.

I checked C1/C4 by opening every cited node's statement, not its proof. I checked that the new child has no dependencies back to its parent or this item. The four off-unit statements are declared as generic tools in split_report.tool_uses with their exact purpose; definitions are notions. No proof step exceeds 2000 characters. The original statement, the chapter and the unit are unchanged; the item is not a unit key node, so no realized fields are written. Nothing was written outside the assigned sandbox, no compiler was run, and no agents were started.

## Unfinished work

Only the deliberately statement-only child Tag 0AB6 remains for a later one-level split. The item's proof is complete relative to its cited statements. Server validation and direct delivery follow this report.
