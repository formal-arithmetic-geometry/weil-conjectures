# Worker report: lem-trf-normalized-projective-closure

Group Q116, stage 1, 2026-10-23. Direct delivery and self-review under the explicit brief.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-normalized-projective-closure.json: item, split; no full Mathlib match.
- citations.json: exact statement quotations for every use in every proof step.
- report.md and searches.jsonl: report and genuine logged searches. No new nodes; no new Mathlib leaves.

## Attachments

None. Searched the project library for the exact blueprint tag and for projective closure, normalization and smooth proper completion. Read WeilConjectures/Compactification/AffineProjective.lean:44–85 and AlgebraicGeometry/Curve/Compactification.lean:79–145. AffineSpace.projectiveClosure_spec covers the specified closure's compactification properties only. IsCurve.exists_projectiveClosure is existential and does not prescribe the given embedding or normalize it. The smooth-completion theorem requires a smooth geometrically connected input and constructs another compactification. None is an exact attachment for our item, whose affine curve may be singular. No Lean was written or compiled.

## WANTED

None. All sources used are available in literature/stacks-project.

## Audit findings and changes

The item had no proof. Its statement and statement dependencies are unchanged. The imported source's broad compactify-then-normalize instruction is realized using the existing DAG, rather than by introducing nodes restating its clauses. Read current blueprint/latest for the ancestor lem-trf-local-term-locality (statement and proof), the unit sk-i-curve-zero and chapter sec-trace-formula, and current normalization-exists and normalized-curve-smooth statements. This geometric subsidiary input retains the inherited closure-then-normalization route; it does not alter the contracting-correspondence argument or the fixed unit/chapter. Blueprint searches for projective closure, normalization, normalized projective, nonsingular, and normalization of gave no node stating this entire specified construction. The projective-closure existential result and normalization component results are strictly partial.

Mathlib searches were run with the prescribed msearch.py for this item, using LeanFinder (two phrasings), Loogle, grep and LeanSearch, all successful. Read the returned relative-normalization results in Mathlib/AlgebraicGeometry/Normalization.lean:340–366 and 581–633. Smooth base-change compatibility of normalization does not assert that a normalized curve is smooth over a perfect field; relative-normalization integrality is only one component. The previous item searches are retained and the current exact queries and results appended. There is no search invented from a desired result.

A concrete C4 repair during preparation: lem-sc-normalization-exists states finiteness, surjectivity, birationality, dimension and properness, but does not explicitly state integrality of its source or spell out the induced function-field isomorphism. I therefore also cite the already existing, more general lem-per-finite-curve-normalization-regular, verifying that X is Noetherian first. I do not take those assertions from the proof of normalization-exists. I checked Stacks' tag table and corrected the birational-definition tag to 01RO.

## Not duplicates

No new nodes, so no new/existing same-tag pairs. Existing det-nagata-affine-opens-projective, lem-trf-reduced-scheme-image, lem-sc-integral-locally-algebraic-opens-dimension, lem-sc-normalization-exists, lem-per-finite-curve-normalization-regular and lem-sc-normalized-curve-smooth are reused. Their statements are actually opened and read, not inferred from their titles. No cited dependency transitively depends on this item (checked by reading the dependency graph).

## Review by Q116

I read curves.tex Tag 0BY1 (theorem-curves-rational-maps), especially its final alternative which compactifies first and normalizes afterwards, and Tag 0BY3 (lemma-nonsingular-model-smooth). For reducedness I read morphisms.tex Tag 056B (lemma-scheme-theoretic-image-reduced). For dimension I read varieties.tex Tag 0A21 (lemma-dimension-locally-algebraic), specifically (3). For normalization I read varieties.tex Tag 0BXR (lemma-normalization-locally-algebraic), morphisms.tex Tags 035Q (lemma-normalization-normal), 0BXC (lemma-normalization-birational), and the definition of birational morphism Tag 01RO. I also read resolve.tex Tag 0BI4 (lemma-resolve-curve), its (4) implies (2) paragraph, and properties.tex Tag 0BX2 (lemma-normal-dimension-1-regular), the sources of the existing normalization theorem used for integrality. There are no new-node sources to review.

Step 1 uses exactly the closure specified in det-nagata-affine-opens-projective: finite-type affine U, immersion into affine space, standard chart, and scheme-theoretic image in projective space. Its base hypothesis holds for Spec k. Its statement gives projective and proper X and dense open j. def-weil-proper-morphism explicitly includes finite type. No alternative existential compactification is substituted.

Step 2 uses the reduced, nonempty, irreducible characterization written in def-pc-integral-scheme and the actual reduced-image statement of lem-trf-reduced-scheme-image. Its reduced-source hypothesis holds because U is integral. The irreducibility of the closure is proved explicitly through intersections of nonempty opens; it is not left as an uncited algebraic-geometric theorem. The same integral-scheme characterization yields integral X.

Step 3 uses the complete statement of lem-sc-integral-locally-algebraic-opens-dimension. X is integral and finite type and j(U) is nonempty, so every hypothesis holds. An arbitrary dense open of an arbitrary scheme would not suffice, which is why the locally algebraic theorem is cited.

Step 4 applies lem-sc-normalization-exists only after establishing integral finite-type X. X is proper by Step 1 and has dimension one by Step 3. Thus the theorem gives finite nu, proper C and the dimension equality. lem-weil-pbc-finite-type-over-noetherian makes X Noetherian over the already verified Noetherian field base. The statement of lem-per-finite-curve-normalization-regular then directly gives integral C and the function-field isomorphism induced by nu. Its finite-normalization hypothesis was proved first. The proof does not assume U normal or smooth. Properness includes finite type by the cited definition.

Step 5 uses lem-sc-normalized-curve-smooth, whose exact statement concerns normalization of integral finite-type dimension-one X over perfect k. These are precisely our established hypotheses. Perfection is not dropped, and smoothness is not inferred merely from normality without this theorem.

Step 6 cites scheme sobriety for the existence and uniqueness of generic points, the open-immersion definition for the actual restricted sheaf, and the function-field definition for generic stalks. The neighbourhoods inside the open chart are cofinal, which explicitly identifies the actual stalk homomorphism as an isomorphism. For nu, the already cited birationality statement means the generic-point and generic-stalk assertions by Tag 01RO. This is elementary unpacking, not a new normalization lemma. Step 7 explicitly checks both stalk homomorphisms on every base scalar a and checks the inverse map the same way, establishing the specified composite as a k-isomorphism.

I checked B–E point by point: self-contained unchanged item; correct tag/label pairs; every non-elementary invocation has a node and a verbatim statement quotation; no use of a cited node's proof; no cycles; no clause-restatement new nodes; no SGA route; no hidden comparison in a long step. All steps are below 2000 characters (the entire assembly is below 3000). Off-unit geometric tools are declared in split_report.tool_uses because this trace unit has no other closure, dimension or normalization results; no proof route is replaced.

Edge cases: n=0 admits no such dimension-one closed affine subscheme of Spec k, so the implication is vacuous. Empty U is excluded by integrality and dimension one. For U=A^1 the result is the usual P^1 model. For an affine cusp, j identifies the original singular U with its open image in X, while normalization changes that open; no lift of U as an open subscheme of C is asserted. Geometric integrality is not assumed or concluded: constants can be a nontrivial finite extension of k, and all identifications remain k-linear. Imperfect fields, where regular need not imply smooth, are excluded exactly where used. Properness of C is obtained from normalization-exists, rather than guessed from its topology.

## Unfinished work

None in the stage-1 split. The cited existing unsplit nodes remain their own tasks; no claim of a completed Lean proof is made. Delivery checks are recorded below after execution.
