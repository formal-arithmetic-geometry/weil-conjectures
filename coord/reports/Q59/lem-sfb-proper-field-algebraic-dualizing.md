# Q59 — lem-sfb-proper-field-algebraic-dualizing — route-pivot repair

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-field-algebraic-dualizing.json: ten-step repaired proof, revised proof dependencies and tool-use declarations. Removed the redundant dropped definition citation from the statement and stmt_deps; the mathematical assertion is unchanged. No new nodes and no Mathlib leaves.
- citations.json: 34 verbatim statement quotations, one for each current step/node citation.
- report.md: this repair and its review; the complete earlier report follows below as superseded history.
- repair_split.py: sandbox-only script producing the repaired node and citation list. The earlier write_split.py is retained as historical work and must not be rerun: it writes the returned proof.

## Attachments

None. Rechecked the project Lean sources by the exact id and dualizing/Dualizing concepts; the hits concern etale or pro-etale coefficient duality, abstract monoidal duality and other assertions. They do not state this coherent algebraic-duality result. No Lean edits, builds or compilers were used.

## WANTED

None. All cited sources are available locally.

## Return repaired

The return identified a substantive route failure: the proof newly used the dropped polynomial-extension and dualizing-localization nodes, as well as an inherited dropped definition citation. I compared the retained delivered split with the current repository node: the current node remains statement-only and agrees with the returned mathematical statement. I retained the prior split, sources, report and all recorded search results as source material; the old report below explicitly documents the superseded route. No released repair-note file exists locally. The explicit repair instruction in this task is the authority for revising the route.

1. Removed the dropped definition reference from the statement and stmt_deps. The statement itself already gives bounded coherent cohomology, finite injective dimension with its bounded-injective meaning, and the homothety isomorphism, so this removes no mathematical condition and changes no hypothesis. The nodal-relative-dualizing-line and complete-local-coherent-duality callers retain exactly the same assertion.
2. Replaced the global polynomial-dualizing argument by regularity of each polynomial localization, using the existing polynomial-regularity node and the regular-local bounded injective resolution node (0AWX). The cyclic cohomology and scalar-map conditions of the local ring in degree zero are proved explicitly in step 3. There is no claim that P[0] is globally dualizing.
3. The determinant identification of the top polynomial differential module remains in step 4. Step 5 now states the elementary shift argument conditionally and applies it only to the local output of finite-map transfer at step 10. It no longer assumes the old global transfer result.
4. Steps 6 and 7 now establish finite cohomology independently: a degreewise finite free resolution (possibly infinite), the projective derived-Hom model and the Noetherian submodule theorem prove finite generation; flat coherent RHom base change, the dimension-n maximal polynomial localizations and their global-dimension bound prove vanishing above n. The annihilator argument explicitly detects zero from maximal localizations. The existing finite-cover coherence and boundedness gluing argument is retained as step 8.
5. Step 9 retains the exact-stalk identification but replaces dualizing localization by coherent derived-Hom base change for the bounded finite inputs B[0] and P[0]. It explains the quotient-localization equality B tensor_P P_q = B_p and the action compatibility of the canonical comparison in the derived B_p-category. Step 10 applies the accepted generic finite-map transfer (0AX0) only over the Noetherian finite map P_q to B_p. Step 5 then handles the shift. No polynomial-extension or dualizing-localization node is used.

This is a changed mathematical proof, not an unchanged rebase. The three forbidden dependencies are absent from statement dependencies, proof dependencies and all uses. I also checked every current direct dependency against the local coord/route-pivot-dropped.txt: none is dropped. The global statement is true; no STATEMENT-DISPUTED correction is needed.

## Searches and reuse

Read all five retained Q59 search-log results and the inherited search records. Their questions have not changed: they test this exact proper-field coherent dualizing assertion and finite injective dimension of its derived stalks. The adjunction hits are ordinary sheaf/module adjunctions, and the injective-dimension hits do not prove the assertion. No repeated search or invented search record was added. All extra tools in the repaired proof already exist in the DAG, so there are no new node search obligations. I searched and opened the existing finite-free resolution, Noetherian submodule, projective Hom, localization-flatness, polynomial maximal-localization dimension and regular-local global-dimension statements before citing them.

The chapter/unit records were read alongside the current latest blueprint direct-images proof (3) and its unit. The marked coherent-duality prerequisite is below that unit route; only the local commutative-algebra realization of the prerequisite changes. This follows the maintainer's expressly suggested repair, uses no SGA source, and alters neither chapter nor unit. The existing detailed blueprint ancestry is retained. Generic tools from other units are declared in split_report.tool_uses with their actual local-algebra purposes; in particular finite-map transfer is the 0AX0 commutative-algebra tool expressly accepted by the return.

## Not duplicates

No new nodes. All extra inputs are citations of existing nodes. No new node restates the item or one of its clauses.

## Review by Q59

I read the source conclusion in duality.tex lemma-shriek-dualizing (0AA3, line 4491) and the proper-field normalization examples starting with example-proper-over-local (0AWI, line 5853). The original source proves preservation of dualizing complexes by polynomial extension and a quotient; that global input is precisely the unavailable route. The repaired proof is marked proof_origin.by = agent, since it supplies a different local-algebra proof of the same consequence. I read dualizing.tex lemma-regular-gorenstein (0AWX) and lemma-dualizing-finite (0AX0), more-algebra.tex lemma-base-change-RHom (0A6A, case (3)) and lemma-RHom-out-of-projective (0A66), and algebra.tex lemma-resolution-by-finite-free (00LP), lemma-Noetherian-basic (00IK), lemma-flat-localization (00HT), lemma-dim-affine-space (00OP), proposition-finite-gl-dim-polynomial-ring (00OQ), and proposition-regular-finite-gl-dim (00O7). The top-differential local model, finite-cover gluing and stalk sources from the earlier review remain applicable. There are no new statements to audit against sources.

Steps 1 and 2 retain their earlier arguments. I reread the actual cited statements: properness includes finite type and separatedness; the finite-type definition supplies a finite affine cover, Noetherian permanence and finite-presentation apply over a field, and separated-implies-quasi-separated supplies the remaining finite-presentation hypothesis. The field-flatness node applies to every scheme over a field. The proper-flat polynomial model explicitly states the derived coinduction formula, the affine equivalence is induced by termwise tilde and sends k[0] to the structure sheaf, and the right-adjoint uniqueness statement identifies the arbitrary given a with that model's right adjoint. No smoothness assumption enters.

Step 3 uses the polynomial regularity statement for all prime localizations, not just closed points. The bounded-injective node assumes a regular local ring and gives exactly a bounded injective representative of its ring in degree zero. The derived-Hom projective-resolution statement applies to the one-term free resolution of A over A. Evaluation at one identifies the homothety with the identity; cyclic cohomology is finite. Thus every hypothesis of the later finite-map transfer input is checked without the dropped definition node.

Step 4 uses only the polynomial differential basis and the exterior algebra definition; the determinant and its inverse are written out, including the zeroth exterior power. Its conclusion is the derived B-linear isomorphism L_B = M_B[n], with the action specified by the existing model. Step 5 checks shifts on the three explicit conditions and checks the scalar map rather than merely the endomorphism object. It is elementary and conditional, with no auxiliary dependency or global claim.

Step 6 uses the finite-free resolution statement exactly as stated: it supplies infinitely many finite free terms if necessary, not a bounded finite free resolution. The projective-resolution Hom statement computes the underlying derived Hom. The Noetherian submodule statement is applied to the finite free terms of its dual to make cycles finite, and finite generation passes to their quotients. The action inherited from P factors through the quotient B, so these generators are also B-generators. The nonnegative degrees give the lower bound. Step 7 applies the flat coherent base-change statement to B[0] and P[0], both bounded with finite cohomology over P; it does not assume its output M_B is already bounded. The localization-flatness node supplies flatness, polynomial regularity supplies regularity, the maximal-localization dimension node gives exactly dimension n, and the regular-local global-dimension node supplies a projective resolution of length at most n. The projective Hom node gives Ext vanishing, and the explicit proper-annihilator argument detects zero at all maximal localizations. These are the uniform bounds needed later.

Step 8 retains the previous affine comparison and gluing proof, now taking its finite modules and explicit [-n_i,0] bounds from steps 6 and 7. The derived tilde/homology statement applies because the equivalence in step 2 is induced termwise, the finite-type affine criterion and locally-Noetherian coherent criterion give coherent cohomology on each chart, and the finite affine cover allows a minimum and maximum. The empty scheme is treated separately. I reread those node statements: none requires smoothness, equidimensionality or a single polynomial presentation covering all components.

Step 9 cites the affine stalk-ring and tilde-stalk statements for the actual prime p, and exact stalks preserve the quasi-isomorphism from the chosen sheaf-complex model to K. The inverse image prime q makes B tensor_P P_q exactly B_p because every b outside p lifts outside q. The same flat coherent base-change node applies to the bounded finite inputs as in step 7. The canonical map respects the coinduced action, so its derived isomorphism is in D(B_p), not merely a per-degree claim or an unsupported change of scalar structure. No injective module is localized in this argument.

Step 10 uses exactly the finite-map transfer statement: A and its quotient D are Noetherian; the quotient is generated by one as an A-module; A[0] has finite cohomology, the bounded injective model and homothety from step 3. Its conclusion explicitly gives all three output conditions with the coinduced D-action. Step 5 proves these for the shift, step 9 identifies that shifted object with the actual stalk, and step 8 gives global bounded coherent cohomology. This is the assertion of the item in arbitrary dimension and over an arbitrary field.

I checked B--E against the changed files, with C1/C4 in particular: every non-elementary input above has its existing node, and each cited node's statement was opened and compared to the step. The 34 citations are literal substrings of those statements, not quotations from their proofs. All ten steps are under 1200 characters, so no long step hides an independent comparison or lemma; the quotient fraction identification, determinant, shift and maximal-localization zero test are written elementary arguments. There are no new definitions or statement-only nodes, no new search claims, no clause-relabelling split and no appeal to 0AA3 as a black-box dependency.

Small cases were checked with this local proof: the empty scheme has zero K and no stalk conditions; Spec k permits n=0 and the identity quotient; P^1 has chartwise n=1 and the usual shift; finite nonreduced k-algebras are covered by finite coinduction over regular local polynomial rings without a reducedness assumption; disconnected or mixed-dimensional components use their own polynomial presentations and the finite cover combines their bounds. No normalization by a single component dimension is asserted. No mathematical hypothesis or conclusion was changed.

## Validation and outstanding work

The required initial dry run of the retained returned version passed mechanically (receipt b17cf0231d8); that did not resolve the mathematical return. The current proof is substantively changed as above. The repaired ten-step split passed server preflight at 901bd5b8a86 (OK, not pushed). All 34 verbatim citations passed local comparison; every direct dependency is absent from the route-pivot drop list, and none of their dependency closures leads back to the item. A final dry run includes this validation record; the subsequent direct-delivery commit is reported in the worker's final answer. No mathematical issue remains open.

---

## Earlier delivered report (retained history; superseded proof route)

The following is the earlier report verbatim. Its polynomial-extension and dualizing-localization route, and its statement-dependency description, are superseded by the repair above.

# Q59 — lem-sfb-proper-field-algebraic-dualizing

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-proper-field-algebraic-dualizing.json: statement split into seven proof steps; unchanged statement and statement dependencies; no new nodes, no new Mathlib leaves.
- citations.json: verbatim statement quotations for all 27 step/node citations.
- searches.jsonl: the five searches run through the required msearch command; the item retains its inherited searches and adds these actual current-group results.

## Attachments

None. Searched lean/WeilConjectures for the exact item id and for dualizing/Dualizing. The hits concern etale/pro-etale dualizing objects, abstract monoidal duality, and unrelated commutative algebra; none proves the coherent algebraic dualizing assertion. No Lean was written and no compiler was run.

## WANTED

None. All mathematical sources needed are present in literature/stacks-project.

## Corrections and scope

The item was statement-only, and its statement is true without adjustment. It is a specialization of Stacks 0AA3, whose actual proof uses polynomial extension and quotient duality; merely adding a new node stating the general 0AA3 theorem would not be a split. Instead the proof follows those two operations and cites the existing nodes for both. The existing proper-flat polynomial model applies because any scheme over a field is flat and finite type over a Noetherian field is finite presentation. Uniqueness of right adjoints explicitly handles the arbitrary chosen a in the statement. Examples 0AWI and the following equidimensional-over-field example explain normalization; their equidimensionality restriction is unnecessary here because no particular cohomological degree is claimed.

No stage-1 repair note exists. The sandbox had only dispatcher markers when opened, so there was no previous split to overwrite. Read the current chapter/unit records and latest blueprint sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, specifically (3). The current blueprint has no node stating this coherent-duality support lemma. The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor prints None; preserved that ancestry rather than inventing a blueprint ancestor. Its detailed from.place and via chain locate the marked plurinodal alteration prerequisite. No chapter/unit change or route departure is made.

## Searches and reuse

Ran both LeanFinder phrasings, Loogle with `"AlgebraicGeometry", "dualizing"`, grep with `dualizing|injectiveDimension`, and LeanSearch with the recorded proper-pushforward query. Read all returned signatures. The sheaf/module pushforward adjunctions are pullback-left-adjoint statements; they give no right adjoint of derived proper pushforward. InjectiveDimension predicates and localization of finite injective dimension of individual modules do not give the derived algebraic-dualizing assertion. Loogle returned zero hits. All five services succeeded for this group; the earlier inherited LeanSearch unavailability remains historical. Read Mathlib/RingTheory/LocalProperties/InjectiveDimension.lean around localizedModule_hasInjectiveDimensionLE and Mathlib/CategoryTheory/Abelian/Injective/Dimension.lean to confirm their scope.

Searched the whole DAG by dualizing concepts and Stacks tags 0AA3, 0AWI, 0A7J, 0A7G, 0BV2 and 01XZ; used tools/blueprint_refs.py search for dualizing, algebraic dualizing, polynomial model and proper over a field, and read the returned mathematical candidates. Reused polynomial extension, finite-map dualizing transfer and localization; the normalized local quotient node is too narrow for nonlocal polynomial rings and is deliberately not used. Reused the existing proper-flat polynomial-model statement instead of creating another affine-local duality comparison. Checked all proposed dependency closures for a cycle back to the item: none.

## Not duplicates

No new nodes. In particular there is no new general shriek-preserves-dualizing node, new field base-case node, new shift-invariance node or new affine coherent-gluing node. Their needed special arguments occur in the item's own steps.

## Review by Q59

I read duality.tex lemma-shriek-dualizing (0AA3) and the preceding remark-local-calculation-shriek (0BV2), as well as definition-dualizing-scheme and lemma-equivalent-definitions. I read dualizing.tex definition-dualizing (0A7B), lemma-dualizing-polynomial-ring (0A7J), lemma-dualizing-finite (0AX0), its quotient corollary (0A7I) and the localization input 0A7G. I read the examples near 0AWI to verify that our result does not require the source example's equidimensionality, and checked the proper-flat model's literature places 0E2X/0E4P. I also read coherent.tex lemma-coherent-Noetherian (01XZ), the affine tilde/stalk source 01HV, and algebra.tex 00FN/00FP. There are no new nodes needing separate source reviews.

Step 1 uses the actual definitions of properness and finite type to choose a finite cover of finite-type affine k-algebras. The cited Noetherian permanence theorem applies because a field is Noetherian; the finite-presentation theorem then applies to each chart. The locally-Noetherian and finite-presentation definitions are used exactly as stated. I added the existing separated-implies-quasi-separated lemma after checking the proper-flat input really asks for finite presentation, and cited the field-flatness statement, which imposes no smoothness or finite-dimensionality condition.

Step 2 uses the proper-flat model's statement, which explicitly supplies both the right adjoint and the canonical derived isomorphism with RHom_P(B,Omega^n)[n]. The hypotheses were established in step 1. The affine derived equivalence explicitly sends the ring in degree zero to the structure sheaf. The unique-right-adjoint node states that its counit transposes are mutually inverse, so it applies to the given a and the model theorem's right adjoint. This avoids silently choosing a different K.

Step 3 proves the field base case directly, including extension of a functional by a complementary basis and the identification of the scalar map by evaluation at 1. The polynomial-extension node applies to all Noetherian rings and all algebraic dualizing complexes, not just local or normalized ones, and its termwise tensor formula gives P[0] after each step. The same Noetherian permanence statement supplies the successive polynomial rings. No finite injective dimension is inferred just from flatness.

Step 4 uses the polynomial differential basis statement exactly for Omega^1; its top wedge is trivialized by the determinant map with the inverse written explicitly. The exterior-algebra definition supplies multilinearity and alternation. Since B is the quotient of P, it is generated by 1 as a P-module. The finite-map transfer node states all three dualizing conditions, including a bounded injective representative with the natural B-action. This is the general nonlocal finite-map result; the narrower normalized-local quotient node would not justify this step. The resulting derived isomorphism is stated in D(B), never only degree by degree.

Step 5 is the elementary shift argument from the three clauses of the definition. Both Hom arguments are shifted together, so the homothety map is the scalar identity under the cancellation. This is why a local shift of n does not require purity or a common dimension among components.

Step 6 reads the derived tilde-cohomology comparison's statement, whose hypotheses hold for the termwise-associated-sheaf affine equivalence. The finite-type affine criterion converts the already finitely generated cohomology modules to quasi-coherent finite-type sheaves; the 01XZ node then gives coherence on each Noetherian chart. Bounds are glued only over the finite cover from step 1, by taking the minimum and maximum. Locality of coherence is expanded from its definition, and the empty-scheme case is handled separately so that no maximum of an empty family is used.

Step 7 uses the affine open stalk-ring localization statement, the tilde-stalk module localization statement and exact stalks. Termwise localization therefore identifies the actual derived stalk with localization of the affine complex. The localization node takes an arbitrary algebraic dualizing complex over a Noetherian ring and concludes it remains one after localization, precisely what is needed here. Its conclusion includes finite injective dimension and homothety, by the cited definition. This is a derived-object identification, not an inference from an unproved per-degree comparison.

I checked delivery-errors B through E point by point: there are no new unsplit statements carrying proofs, no missing new-node hypotheses, no invented search records, no clause-restating auxiliary nodes, no uncited non-elementary appeal to 0AA3 itself, and no use of a node's proof as its public interface. Every cited node was opened and its statement compared with its use; citations.json quotes those statements literally. Every proof step is under 1000 characters, so there is no step exceeding the 2000-character review threshold. Generic tool uses outside the unit are declared in split_report.tool_uses with a reason. No SGA source is cited.

Small cases checked: C empty; C=Spec k with n=0; a finite nonreduced k-scheme, where the finite dual is Hom_k(B,k) rather than B in general; P^1 with its shifted dualizing line; and a disjoint union with components of different dimensions. The finite-cover bound argument accommodates different local intervals and never imposes connectedness, equidimensionality, reducedness, smoothness, perfection of k, or characteristic restrictions. All assertions hold over inseparable and imperfect fields as well.

## Unfinished work

None in the authorized stage-1 split. New proof obligations were not created: the needed inputs already have DAG nodes. Required server dry run and delivery are recorded below after execution.

## Validation

First deliver.py --no-push exited 1 on three quotations shorter than the minimum 40-character quotation requirement. Expanded those quotations to the complete cited statements; no mathematical change was required.
