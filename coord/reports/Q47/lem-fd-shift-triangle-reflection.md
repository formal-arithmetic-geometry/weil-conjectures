# Stage-1 delivery: lem-fd-shift-triangle-reflection

## Files written

- dag/nodes/sec-fourier-transform/lem-fd-shift-triangle-reflection.json — statement, split into seven steps; no Mathlib match for the whole item.
- citations.json — verbatim statement excerpts for every cited node in every step.
- searches.jsonl — actual msearch results; the item's pre-existing Q11 searches are retained in its JSON alongside these new searches.

No new nodes; no new Mathlib leaves. The statement, statement dependencies, inherited blueprint provenance, and other imported fields are unchanged. All writes are in the assigned sandbox. No Lean was written or compiled.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for common-stage/pair-category shift, exactness and reflection. CategoryTheory.StageSystem.descFunctorCommShiftIso, descFunctor_commShift and descFunctor_isTriangulated in CategoryTheory/StageSystem/Exact.lean cover the generic forward construction, but no declaration found states all of this item, including its finite reflected model and specified image of the lifted triangle isomorphism. They are reference material, not claimed attachments.

## WANTED

None. The argument is explicitly agent-written; no unavailable external source is silently claimed.

## What needed repair

The live item had no proof. I expanded the argument retained as original steps 6–8 in coord/reports/Q11/lem-fd-common-stage-comparison-descent.md. In particular, the exact quasi-inverse used in its reverse argument needed a cited theorem, and the phrase about lifting triangle equations needed the third-square calculation. Both are now explicit. No statement dispute was found.

## Not duplicates

No new nodes were created. I searched the whole DAG and blueprint for shift triangles, distinguished triangles, exact equivalences, quasi-inverses and inverse exactness, and read the nearby candidates. lem-trf-exact-equivalence-inverse is precisely the generic inverse-exactness fact needed, and is reused as a Mathlib leaf. lem-weil-pbc-pair-functor-shift-coherence concerns PBC-to-PBC systems; lem-sf-framework-common-stage-descent concerns framework-to-framework systems, and neither is directly applied to these distinct framework/PBC categories. lem-sbc-coherent-pair-functor-descent is a generic alternative for natural-transformation descent; the present short representative computation proves exactly the needed naturality without invoking its Karoubi clause or adding another node. The item retains blueprint.from.node def-fd-trace-function with the existing via chain and precise place; blueprint searches found no same statement.

## Mathlib searches

Every new search was run with msearch.py and read. The inverse searches found Equivalence.IsTriangulated.mk', its inverse instance, and their symmetric forms. I read Mathlib/CategoryTheory/Triangulated/Adjunction.lean:184–207: the forward-exactness constructor at line 202 and inverse instance at line 195 match the existing leaf, including compatible inverse shifts. The second semantic search found Functor.map_distinguished_iff and triangle-map full-faithfulness in Triangulated/Functor.lean; these presuppose the descended shift and exactness and do not state this item's explicit finite-model assertions. The item-level second phrasing returned map_distinguished_exact, distTriang_iff and mapTriangle constructions, while grep for StageSystem, PairCategory and common-stage triangles returned zero Mathlib hits. LeanSearch and Loogle were available. No service failure was recorded as mathematical absence.

## Review by Q47

I read the fixed Fourier chapter, unit sk-def-trace, and current main-20261015 def-fd-trace-function.md. The blueprint's final sentence uses the PBC coefficient category; the argument here is the same auxiliary comparison route as the original steps 6–8, not a replacement of a trace-function proof. I also read the full statements of every proof dependency: the two pair-category definitions, finite-stage pair category, common-stage cones, common-stage calculus, triangles with shift, triangulated category, and the inverse-exactness Mathlib leaf. For the latter I checked the Mathlib declarations above and Stacks derived.tex, Tag 05SQ, lemma-exact-equivalence (including its componentwise full-faithfulness lifting argument). No SGA source is used.

Step 1 uses the framework pair-category definition for representative morphisms and shifts, and common-stage calculus for the actual scalar-conjugated shift formula. Exact naturality of j and finite naturality of delta are assumptions of the item, not uncited conclusions. I checked the displayed equation P(delta) j_shift = sigma_p inverse times j[1] times delta_M times J(sigma_s), including its direction. Substitution at Y cancels J(sigma_s,Y inverse), finite naturality moves delta through J(u[1]), and substitution at X gives the final equality. Both ends are the required pair representatives at the same M. This is elementary substitution in the hypotheses and definitions.

Step 2 uses the same pair data and the explicit identity/composition normalization of def-weil-pbc-finite-stage-pair-category. Both products of delta and its inverse are represented by the identity at E. Identity j at E proves the inclusion equality on morphisms. Integer comparisons use the iterates and inverse iterates of the prescribed finite comparison; zero and addition coherence equations can be checked at E because the components and canonical shift maps involved are all finite-stage maps. No hypothesis about arbitrary alternative shift structures is inserted.

Step 3 uses def-weil-pbc-common-stage-cones for precisely the third arrow sigma inverse times p_u, the finite pair definition for identities and composition, common-stage calculus for the shift of [M,1], and def-weil-pbc-triangles-with-shift for the three-square criterion. I verified a[1] is [M,sigma], so the third square is sigma times sigma inverse times p_u = p_u. The other endpoint and the cone have the claimed source and target; using [M,1] in the reverse Hom gives its inverse. This checks the finite-stage inclusion model, rather than assuming it from a definition that only mentions common-stage cones.

Step 4 uses def-weil-algebraically-closed-coefficients for a finite distinguished source model, def-weil-triangulated-category for the meaning of exactness, and the cone definition for distinguished finite target inclusions. The exactness of J_M is a stated hypothesis; the third-arrow comparison is the finite delta from step 2. The model of a distinguished triangle need not be literally its original objects, since the source definition and functoriality handle the isomorphism.

Step 5 uses lem-trf-exact-equivalence-inverse exactly as stated: finite categories are triangulated and J_M is an exact equivalence; R_M has the induced shift so its counit commutes with shifts. It does not assume inverse exactness without citation. The source pair definition makes the inclusion of R_M A distinguished, and the triangle-map definition checks the counit. I fixed gamma to be e inverse composed with alpha, so the demanded image of the lift will be determined.

Step 6 uses only the assumed Hom bijections and the explicit triangle-map definition; it follows the elementary component argument also seen in Stacks 05SQ, without invoking any extra theorem from that source. Lifts of inverse components are inverse by injectivity of the Hom maps. The first two squares are checked after J. In the third square, naturality d_X' J(a[1]) = J(a)[1] d_X allows cancellation of d_X', followed by Hom injectivity. Thus the lift is a triangle isomorphism and e J(beta) = alpha, not merely an objectwise isomorphism. Distinguishedness then follows from the source pair definition.

Step 7 supplies essential surjectivity explicitly with the finite quasi-inverse and counit, to justify applying lem-trf-exact-equivalence-inverse to J at the pair level. The phrase every quasi-inverse is restricted exactly as in the statement to its induced shift. Both pair definitions explicitly use raw categories; no idempotent envelope enters the proof. The only non-elementary fact imported beyond the pair calculus is the existing inverse-exactness leaf. Common-stage calculus is declared as an off-unit generic tool in split_report.tool_uses; it supplies the same actual shifts already named in the pair definitions. The Mathlib leaf needs no route exception.

I checked hypotheses at each application: W is allowed (noetherian, finite-dimensional, ell invertible), all finite fields lie in the chosen algebraic closure, J_M is an equivalence with its specified exact shift, j is normalized and shift-compatible, and the Hom bijections are hypotheses. I did not assume finite-stage transition functors are faithful or that pair-object isomorphisms are literal equalities. The cases E=F=M and j=1 reduce the naturality formula to finite naturality; zero and identity morphisms reduce the cone third-square computation to the same sigma cancellation; distinct endpoint fields remain at their given common M. A zero category or a zero triangle is included. These checks expose no false edge case. No new statements require a separate small-case audit.

I checked delivery-errors B–E: there are no new nodes that could be elementary, duplicates or clauses relabelled as lemmas; every non-elementary input is a cited statement; the Hom lift is written out; all formulas are ordinary single-escaped TeX; citations.json contains verbatim statement excerpts. All seven proof steps have fewer than 2000 characters, so none hides a long subsidiary argument requiring its own node.

## What could not be finished

Nothing in the authorized stage-1 task remains mathematically open in this split. Independent maintainer review follows delivery.

## Validation

The first server dry run passed at b7db92961da. I then refined the verbatim citation excerpts for shifts, distinguished target triangles and raw categories to quote the precise clauses used. The final dry run and push use these refined citations.
