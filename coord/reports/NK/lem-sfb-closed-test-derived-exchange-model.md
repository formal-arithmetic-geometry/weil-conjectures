# Stage-1 delivery: lem-sfb-closed-test-derived-exchange-model

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-closed-test-derived-exchange-model.json: statement, split into eleven steps using existing nodes; no Mathlib match.
- citations.json: verbatim statement quotations for each step/node citation.
- searches.jsonl: six fresh searches made with msearch.py; the item also retains all inherited Mathlib searches.
- report.md: this report.

No new nodes; no Mathlib leaves. No unit or chapter file changed. The item is not a unit's key statement.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for closed-test/exchange terminology. The hits concern finite-coefficient closed support, generic-fibre exchange, and other statements; none states these derived isomorphisms for arbitrary condensed coefficients, with the specified mate and actual coefficient-map naturality. No source declaration is treated as finished merely because its signature exists.

## WANTED

None. All sources needed for this argument are present in literature/.

## What was wrong or incomplete

The imported item was unsplit, not false: its statement is unchanged. Tags 09BL and 0D6F supply the closed evaluation and localization inputs, but do not themselves state the complete derived internal-module comparison or its coefficient naturality. The proof_origin is therefore agent, and the report distinguishes the source results from the calculation supplied here.

The unit is the inherited sk-thm-sf-ctf-stability. Its clause (vii) and the parent closed-base-change paragraph need this comparison before any geometric proof of invertibility; this split proves no such invertibility and changes no route. The inherited blueprint ancestor is null (confirmed by blueprint_refs.py ancestor), with the precise parent paragraph and full inherited via chain retained. Blueprint searches for closed, closed inverse, inverse image, sections localization and derived exchange found no node with the whole current statement; the finite-coefficient closed inverse-image formula and the etale-abelian termwise exchange have narrower hypotheses/categories and are not duplicates or substitutes for the calculation here.

I caught and repaired a possible overapplication of the exact-left-adjoint composition theorem: global sections need not have an exact left adjoint for arbitrary coefficients. Step 7 instead uses the generic K-injective composition theorem for a_* followed by sections, because a_* preserves K-injectives. The exact-left-adjoint normalization theorem is used only for geometric inverse/direct-image composition.

## Unfinished work

None for this one-level stage-1 split. The proof dependencies remain their own DAG items where not already finished. No Lean was written and no compiler, Lake or build tool was run.

## Not duplicates

No new node is proposed. In particular, the existing set-sheaf closed evaluation, internal-module equivalence, exact weakly-contractible evaluation, section localization, and generic derived-composition nodes are cited rather than re-created. No clause of the item was moved into a new node.

## Review by NK

I read proetale.tex at lemma-closed-immersion-affines and lemma-closed-immersion-affines-apply, Tags 09BK and 09BL, including the proof of (2) explaining why weak contractibility removes sheafification on the chosen test. I read sites-cohomology.tex at the restriction-of-K-injectives lemma and lemma-unbounded-cohomology-of-open, Tags 08FI and 0D6F, and the ringed localization/Leray discussion. I also read derived.tex at lemma-adjoint-preserve-K-injectives, Tag 08BJ, and the general derived adjunction lemmas, Tags 0FND, 0DVC and 09T5. These results are used through existing node statements, which I opened individually. There are no new-node sources to review.

Step 1 uses the internal/section-ring module equivalence, whose statement explicitly preserves underlying sheaves and section groups; exactness and preservation of K-injectivity follow from the equivalence. The locality node explicitly supplies exact inverse image for arbitrary condensed rings and arbitrary morphisms. The module push/pull and lower-star nodes state precisely the underlying functors and base-change section formula, so I did not use a finite-coefficient result for a nonfinite ring.

Step 2 uses the closed-site functor-properties statement for V = v(V) times_U Z, and the closed inverse-image evaluation statement for the value on V. Its passage from sets to abelian groups is naturality for the group operations, and its passage to modules uses the same coefficient/action naturality. The source-affine evaluation theorem states the geometric w-contractible criterion in the relevant section universe, and the weakly-contractible module evaluation theorem states preservation of homology. Both V and v(V) satisfy that hypothesis here. No such assumption is made on T or T_0.

Steps 3 and 4 use the actual module-derived pushforward, not derived functors of the underlying abelian category. The cited right-adjoint theorem requires an exact left adjoint; step 1 supplies this for f and f_Z. Derived section localization states its isomorphism in D(Ab), represented by the degreewise identity on a K-injective complex. Thus it yields derived-object isomorphisms, not merely equal cohomology groups. The exact-functor statement is in sk-def-sfb-derived-categories. The second resolution is of h^*I; I did not assume h^*I is already K-injective or that the closed pushforward is exact.

Step 5 spells out the mate calculation, using the inverse-image unit-section definition, the Kan-extension definition of inverse image, the specified module adjunction, and closed evaluation. The section x on T is represented by the test v(V); the counit evaluates that representative and the triangle identity cancels the inserted unit. This leaves exactly the unit section for a on T_0. This is a short calculation from definitions, not an uncited geometric base-change theorem. The calculation includes the actual coefficient identification rather than replacing module pullback by an unrelated functor.

Step 6 uses the statement of derived-adjunction-from-underived for the normalization by the ordinary counit. The transpose of the proposed chain map is the given pulled-back counit followed by the target resolution, which uniquely characterizes the specified exchange. Step 7 uses the generic K-injective composition statement for a_* and sections and the right-derived universal unit for its canonical normalization. The geometric composition theorem states that the conjugate composition comparison has the composite unit/counit. Ringed derived localization explicitly says its comparisons preserve units and counits. Thus the quoted statements suffice to identify the map, and not only its source and target.

Step 8 uses the K-injective Hom statement to compare any two representatives and any derived morphism; it does not ask for a chain lift into a non-K-injective target. Closed evaluation is explicitly natural in both the sheaf and admissible test. Step 9 uses the ordinary localized ringed-site statement with its identity-on-sections formula, and its derived version with adjunction compatibility, for pro-etale base change on localizations. Only base-changed admissible tests enter that claim. Pullback and geometric direct-image compositions use the canonical comparisons, so an isomorphism of squares transports the units themselves.

Step 10 uses the exactness and underlying-identity clauses of scalar restriction, and the ordinary scalar-adjunction identifications in lem-sfb-internal-section-scalar-adjunction. The definition of a total right derived pair gives a bijection of natural transformations after precomposition with its universal unit. Accordingly the coefficient comparison is obtained by deriving the ordinary identity square; its compatibility with evaluation and the unit-section calculation follows by comparing these ordinary squares before applying that bijection. I explicitly did not identify Res of a K-injective resolution with a K-injective resolution and did not assert invertibility of this comparison. The input is the actual module morphism K to Res N. Step 11 uses the ordinary tensor adjunction unit, whose displayed formula is in the cited internal/section scalar-adjunction statement; it does not substitute derived scalar extension for that ordinary tensor.

I checked empty affine tests, zero modules and zero coefficient ring: section complexes and all unit formulas give the zero objects/maps with the same comparisons. For I = 0 (identity closed immersion) the geometric square and closed-site lift give identities and the triangle identity yields identity exchange. For I = A (empty closed subscheme) only the empty tests remain and both derived section targets are zero. Arbitrary affine f, arbitrary ideal I, nilpotents and unbounded-above K introduce no finite-type, reducedness, flat coefficient-change, or cohomological-dimension hypothesis; the calculations use K-injectives and exact test evaluation. All eleven proof steps are below 2000 characters, and none hides a new lemma: non-elementary localization, evaluation, K-injective, and normalization facts are existing cited statements.

All off-unit proof citations are declared as tool uses in split_report. They are generic definitions, evaluation facts and derived-category comparison tools needed to realize the inherited closed-base-change route, not a replacement of the unit's geometric argument. The complete verbatim statements used are recorded in citations.json so that each assertion can be checked against the cited interface.

I checked delivery-errors B–E: self-contained original statement and unchanged hypotheses; all referenced nodes exist; sources have correct Stacks tags; no invented Mathlib search, new duplicate, elementary new node, clause-restatement node, or per-degree replacement; proof dependencies are exactly the union of step citations. I read the actual search results: affine-transition-limit and Zariski module restriction/adjunction declarations do not identify this closed pro-etale derived mate. The six new searches are recorded verbatim from msearch.py, in addition to preserving the inherited searches.
