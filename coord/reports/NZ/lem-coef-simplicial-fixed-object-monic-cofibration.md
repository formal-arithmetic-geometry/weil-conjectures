# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-fixed-object-monic-cofibration.json`: item, proposition unchanged, four proof steps; no new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quotation for the single cited node in step 4; steps 1–3 are explicit elementary arguments.
- This report. The inherited `searches.jsonl` is retained unchanged.

## Attachments

None. Searches of the read-only project source for the item id, its blueprint tag, fixed-object simplicial categories, free extensions and cofibrations found no declaration stating the complete item. Mathlib declarations are not treated as project attachments.

## WANTED

WANTED: Lurie, *Higher Topos Theory*, Proposition A.3.3.8, for the surrounding fixed-object factorization route. The supplied source annotation cites it, but no archival HTT PDF is present in the provided literature directory. The elementary proof below is explicitly agent-written; I do not claim to have read the missing source. This request is retained from the earlier attempt.

## Corrections and limitations

I continued the earlier sandbox rather than restarting it. Its two-step proof used ordinary fixed-object coproduct normal forms to prove free-extension injectivity, then transferred injectivity through a retract with the source fixed. I first repaired the latter calculation to cover arbitrary arrow retracts, which the statement also quantifies over. I normalized the retained TeX backslashes, leaving the mathematical statement unchanged, and restored the current repository's specified blueprint ancestry place.

The required initial dry run then failed: tools/check_dag.py reported a 76-node dependency cycle containing this item, the normal-form node and the fixed-object free-calculus node. That citation reaches the item again through the coherent-nerve/projective-model infrastructure. I removed both direct citations, rather than changing another worker's node or weakening the statement. The final proof establishes faithfulness of a free extension by an elementary separating functor: add a disjoint absorbing zero to each old hom set and send each new generator to that zero. The old-arrow inclusion into this auxiliary category is injective, so the extension cannot identify old arrows. This preserves the parent step's required mappingwise injectivity and uses the existing fixed-object cofibration characterization only after the independent free-extension and retract arguments. No SGA source is used.

## Mathlib searches

I read and retained all existing item search records and the four actual searches in searches.jsonl. The distinct logged queries are also copied verbatim into mathlib_searches with their actual result digests and no-match verdicts. LeanFinder returned simplicial-set cofibration declarations; LeanSearch's second phrasing returned generic retract declarations; Loogle and the logged source grep found no fixed-object enriched-category cofibration theorem. I did not repeat unchanged search questions or invent unrun searches.

I read AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean and CategoryTheory/MorphismProperty/Retract.lean in the pinned Mathlib source. The former identifies cofibrations of simplicial sets with monomorphisms; the latter proves abstract retract stability. Neither proves injectivity for a free extension of ordinary categories or gives the full enriched-category item by one-line specialization. No Mathlib leaf was created.

## Not duplicates

No new nodes were created. Whole-DAG and blueprint searches for fixed-object cofibrations, free extensions and simplicial categories were read. The existing ordinary normal-form node is not used because of the cycle reported above; no replacement duplicate is introduced. The auxiliary zero category and cancellation computations take only a few lines from their displayed definitions and the item's free-adjunction definition, so they remain elementary proof steps. Creating either as a node would split off an elementary construction or restate a clause of the item. The nearby coherent-fixed-vertex-cofibrations node concerns coherent realization of vertex-bijective simplicial-set inclusions, while enriched-fixed-set-model concerns dg categories; neither states this item.

## Review by NZ

I compared the current item with the retained sandbox and read the chapter and unit records. I read the current blueprint ancestor prop-coef-integral-exceptional-adjoint.proof.md, paragraph 2 and its displayed derived-Hom limit calculation: this motivates the coherent coefficient-adjunction infrastructure rather than containing the elementary category argument. I read the parent projective-model-calculus step 17, which uses exactly mappingwise injectivity to embed the two indexing categories in a contractible auxiliary category. The present proof supplies that same prerequisite, below the fixed chapter and unit route. proof_origin remains agent; the missing HTT source is honestly recorded above. There are no new nodes whose sources need review.

For step 1 I checked the explicitly defined category C^0, hom by hom: old-old compositions stay old, and a new zero in either factor gives the new zero with the composite endpoints. A triple with a new zero has the same new zero under either association; an old triple uses only associativity in C. Old identities satisfy both identity laws even on the added arrows. The old-arrow inclusion is a functor and is injective by the disjoint-sum construction. This is an elementary verification with no cited theorem or hidden normal-form result.

Step 2 uses exactly the item's meaning of freely adjoining arrows without extra relations. The functor on the old category and the zero-valued assignment on new generators extend by that defining universal property. No assignment to existing arrows is changed and the target is a genuine category by step 1. Applying the extension to an alleged equality of old images proves equality of the old arrows. The degreewise auxiliary functors are not asserted to be simplicial: only injectivity of the original simplicial map is inferred degreewise. Cancellation in each degree also explicitly proves categorical monicity.

For step 3 I checked all four maps of an arbitrary arrow retract f:A -> C of i:D -> B: u:A -> D, v:C -> B, p:D -> A, q:B -> C. The square i u = v f transports equality after f to equality after i u; step 2 cancels i, and p u = id cancels u. All functors fix O, so every equality stays in the chosen hom set and degree. This repairs the retained proof's unjustified restriction D=A.

For step 4 I opened the full statement of lem-coef-simplicial-interval-lifting. It explicitly states that fixed-object cofibrations are retracts of free simplicial extensions, with degreewise freeness and degeneracy-stable generators. That is precisely the sentence copied verbatim into citations.json. Its extra degeneracy condition entails the item's degreewise-free definition; it is unnecessary for the elementary injectivity argument. No conclusion from the cited node's proof is used. I also read the formerly cited full statements of fixed-object-simplicial-free-calculus and free-factor-category-normal-form before eliminating those cyclic dependencies.

Against delivery-errors B–E, every object is introduced, the only non-elementary theorem used is the single cited characterization, and proof_deps equals the union of uses. No new nodes restate any clause and no off-unit tool is used. I tested empty O, an empty off-diagonal hom set, diagonal identities, existing zero morphisms, invertible old arrows, degree zero, no adjoined generators, and an arrow retract with different domain categories. Added zeros are disjoint even when old zero morphisms exist; zero targets supply images for generators even if the old hom set was empty. No Kan or nonemptiness hypothesis is introduced. All four steps are below 2000 characters and contain one routine construction or equality argument each. The item is not its unit's key node, so no unit record was changed.

No Lean source, compiler, Lake, live project file or launcher was changed; all writes were confined to this item's sandbox.

## What remains

The initial dry run completed with the cycle diagnostic recorded above. The final repaired split must pass a fresh required server dry run before its delivery push.
