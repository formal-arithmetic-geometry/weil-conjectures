## Worker report

Group Q63; item lem-coef-symmetric-inert-active-orthogonality; stage 1 only.

## Files written

- dag/nodes/sec-six-functors/lem-coef-symmetric-inert-active-orthogonality.json: existing statement, split into seven steps using seven existing nodes. No new nodes; no Mathlib leaves. Statement, statement dependencies, source and maintainer metadata preserved.
- citations.json: one verbatim cited-statement quote for every step/node pair (11 entries).
- searches.jsonl: the four actual searches run through msearch.py. The item retains its inherited five searches as well.
- report.md: this report and author review.

## Attachments

None. Searched WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the exact blueprint id and for inert/active/orthogonality, and dag/lean_names_upstream.json for the exact id. No project declaration states this symmetric infinity-operadic result. The inherited node has no Lean declaration attached. No master sorry was treated as proof.

## WANTED

WANTED: Jacob Lurie, Higher Algebra (September 18, 2017), Definition 2.1.1.10, Remark 2.1.2.2, Definition 2.1.2.3, Propositions 2.1.2.4 and 2.1.2.5, printed pp. 178–179, for lem-coef-symmetric-inert-active-orthogonality. Read the Harvard PDF online; it is not archived in literature/. proof_origin.by is agent, as required for an unarchived source. No SGA source is used.

## What changed and what was wrong

The imported statement is correct; it had no proof. I supplied the finite-pointed-set calculations instead of creating nodes for them, then used existing mapping-space and homotopy-pullback lemmas. I did not create a general factorization-lifting node that would relocate the item's argument.

At startup the item had not yet appeared in the shared snapshot and there was no sandbox copy. It appeared during the initial dry-run wait. I then read and used that authoritative node; the initial missing-input diagnosis is resolved and is not a statement dispute. Its original created, chapter, unit and blueprint ancestry are retained. No other DAG node or unit record was changed.

## Unfinished work

None in the stage-1 split. The supporting nodes remain independent work items. No delivery push is authorized or attempted; the sandbox is for the fresh second reader.

## Blueprint and duplicate search

Read dag/chapters/sec-six-functors.json and dag/units/sk-prop-sf-biduality-general.json. The current blueprint places the exceptional-adjoint ancestor in literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md; I read its derived coefficient-adjunction calculation and the current biduality unit text under sec-six-functors-basics. The inherited blueprint.from places this supporting operadic lemma below the middle finite-level mapping-complex comparison, through approximation, module sections and the monadic-bar foundations. I preserved that ancestry; this split makes no change to the coefficient route.

Ran blueprint_refs.py ancestor for the item; after refresh it identifies prop-coef-integral-exceptional-adjoint. Searched the whole imported blueprint for "inert" and "inert active", and searched dag/nodes for orthogonality and inert/active. The blueprint search has no matching operadic statement. Existing nonsymmetric operation-Segal and prism nodes have different conclusions. No new node was necessary. The existing cocartesian mapping criterion, pullback pasting, mapping composition and space fiber-detection statements are the actual needed inputs, all in the assigned unit; no off-unit tool declaration is required. A direct read-only traversal of their statement/proof dependencies found no path back to the item.

## Mathlib searches

The inherited searches include two semantic phrasings, LeanSearch, Loogle and grep. I read their reported hits. For the present split I additionally ran leanfinder for cocartesian inert-edge orthogonality with mapping-space pullbacks; leansearch for inert-active factorization and contractible fillers; loogle with "Operad"; and grep for inert/active and cocartesian/orthogonality. All four services ran successfully. Semantic hits concern inner-horn filling, ordinary model-category factorization, or ordinary-category factorization data. Read Mathlib/AlgebraicTopology/Quasicategory/Basic.lean:35–69 and CategoryTheory/MorphismProperty/Factorization.lean:43–58: these respectively give only the inner-horn condition and ordinary factorization data, not the item's infinity-operadic theorem. Loogle found no Operad hit. Grep found only the FlexibleLinter variables called active and inert. There is no exact or one-line-specialization match. Every new search entry copies the actual query and logged result; no service outage was recast as a negative result.

## Review by Q63

I read Higher Algebra online at Remark 2.1.2.2, Definition 2.1.2.3 and Proposition 2.1.2.5, including its orthogonality and factorization proof, rather than treating the proposition number as a proof. The statement matches its intended inert-cocartesian/active factorization, with full compatible filler spaces; the present statement does not claim the extra retract-closure assertion of the general factorization-system definition. No hypothesis, arity or coherence clause was changed. There are no new node statements or new source citations to audit.

Step 1 cites the actual definitions of nerves/right-pinched spaces and inner fibrations and the symmetric-operad recognition statement. The recognition node explicitly says that p is an inner fibration and has inert cocartesian lifts; its other conclusions are not needed. The proof that P is a quasicategory is a direct horn-lifting check, so the mapping criterion's requirement that both source and base be quasicategories is satisfied. Mapping spaces of the ordinary base are discrete directly from the nerve definition.

Step 2 uses the recognition statement only for its explicit definition of inert pointed maps. The non-discarded input set S gives the inert quotient and active remainder, with the composite verified on every input. It is elementary and is not a new node. Step 3 uses the recognition statement's existence of lifts and the definition node's precise Lambda^2_0 lifting condition. The supplied edges are 01=i and 02=b, so the missing edge is 12=a over the prescribed active map s. The result includes an actual two-simplex, not just an equality in the homotopy category.

Step 4 needs no theorem citation: I wrote the filler formula on each unique retained preimage, proved f vanishes on discarded inputs using activity, and checked both triangles. Inertness makes the pointed map surjective, so uniqueness also covers the basepoint and zero-arity cases. This directly proves the base Hom square is cartesian.

Step 5 uses exactly the mapping criterion's homotopy-pullback square for a cocartesian edge, first with test object u and then v. The pasting node explicitly gives both pasting and cancellation and permits specified commutation homotopies; it is not being cited merely for a definition. I wrote the three rows of both diagrams, checked that their outer rectangles agree, and used the mapping-composition statement for the composition homotopies. Transposition just exchanges pullback factors and reverses their path coordinate. Thus the conclusion is the full mapping-space equivalence requested, not only a bijection of components or a strict commutative-square assertion.

Step 6 uses the enhanced-diagrams definition's path-model homotopy fiber for the entire specified square. The fiber-detection theorem is applied with both bases equal to T and base map the identity, and its equivalence hypothesis is step 5. The fiber of the identity is contracted explicitly by the simplicial max map, so no uncited general contractibility result is hidden. All triangle homotopies and their compatibility with the fixed square path remain part of that homotopy fiber.

Step 7 checks empty S, zero target, zero intermediate set, zero upper-right base set, and empty mapping spaces. The empty operad is harmless because the assertions quantify over its edges/squares. Small nontrivial tests are an inert projection discarding one input followed by an active binary operation, the identity pointed map, and the zero-to-positive nullary operation. In each case the formulas for r, s and d give the expected factorization/filler, while the discarded input must map to the basepoint. No assumption of surjectivity for active maps, positive arity, cocartesian active lifts or presentability enters.

I checked delivery-errors B–E against these files: no unsplit new nodes or duplicates, no hollow definitions, no relocated clause, no circular input, exact cited statements for each non-elementary step, no altered statement, and correctly escaped TeX. citations.json uses verbatim full statement quotes rather than paraphrases. This is the author's self-review, not the second reading.

## Dry run

The first required --no-push invocation reached server preflight and reported exactly one B2 wording issue: step 2 referred to "the item's statement". I replaced that phrase by the explicit active condition $s^{-1}(*)=\{*\}$; no mathematical statement or proof dependency changed. The required dry run is repeated on this repair. No push is attempted.

Additional small-case verification: a direct finite enumeration checked 144 pointed-map factorizations for arities 0–3, and 225 commuting inert/active squares for arities 0–2, including uniqueness against all possible diagonal maps. All passed. The 11 citation quotes were also rechecked against the current shared statements.

## Second reading by Q63

- Item statement: checked against Higher Algebra Definition 2.1.2.3, Remark 2.1.2.2, and Propositions 2.1.2.4–2.1.2.5 (pp. 178–179); inert/active hypotheses, mapping-space comparison, coherent filler data, and arity-zero clause agree.
- Step 1: checked the cited enhanced-diagram, operadic-recognition, and fibration statements; nerve mapping spaces and quasicategory lifting are elementary consequences, verdict PASS.
- Step 2: checked the recognition node's inert definition and the source's active definition; the retained-input construction works also for empty input, verdict PASS.
- Step 3: checked the recognition lift and the stated outer-horn cocartesian condition; the Λ²₀ filler has the required edges and active base, verdict PASS.
- Step 4: checked the pointed-set calculation directly; activity forces discarded inputs to the basepoint and inertness gives the unique diagonal, including zero arity, verdict PASS.
- Step 5: checked the cocartesian mapping criterion, homotopy-pullback pasting, and mapping-composition statements; both pasted diagrams have the required orientations and retain the specified square homotopy, verdict PASS.
- Step 6: checked the enhanced-diagram homotopy-fiber definition and fiber-detection theorem; the identity fiber contraction establishes contractibility with all compatibility data, verdict PASS.
- Step 7: tested empty input, zero target, zero intermediate arity, empty mapping spaces, identity, and a nontrivial inert projection followed by an active operation; all edge cases are covered, verdict PASS.
- New nodes: none; duplicate, elementary, Mathlib, self-contained-statement, and source checks therefore have no new-node findings.
- Changes made: none; the worker's seven-step split and eleven verbatim citation records were already correct. The first dry-run B2 wording repair is recorded above and was rechecked by the passing preflight.
