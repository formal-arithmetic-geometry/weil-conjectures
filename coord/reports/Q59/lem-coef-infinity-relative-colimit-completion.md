# Worker report: lem-coef-infinity-relative-colimit-completion

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-relative-colimit-completion.json`: item, statement unchanged, split into eleven proof steps; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-presheaf-presentability.json`: new statement-only node, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-intermediate-presheaf-kan.json`: new statement-only node, unsplit; no Mathlib match.
- `citations.json`: literal statement quotations for every cited node of every item proof step. `searches.jsonl` is the search command's actual log. `prepare_split.py` is a sandbox-only preparation script, not delivery content.

## Attachments

None. Searches for the exact blueprint tag, the item id, relative colimit completion, cocompletion, and presheaf/Kan/presentability terminology in the read-only project Lean source found no project declaration with this coherent statement. In particular ordinary-category Yoneda extension results cannot attach this item.

## Wanted literature

WANTED: Jacob Lurie, Higher Topos Theory, Proposition 5.3.6.2 and Remark 5.3.6.3 (pp. 412-414), Proposition 5.3.6.11 (pp. 416-417), Lemma 5.3.5.7 (p. 405), Remark 5.5.3.7 (p. 468), Proposition 5.5.4.15 (p. 482), for lem-coef-infinity-relative-colimit-completion.

WANTED: the same book, Remark 5.5.3.7, for lem-coef-infinity-presheaf-presentability.

WANTED: the same book, Lemmas 5.1.5.3 and 5.1.5.5 and Proposition 4.3.2.17, for lem-coef-infinity-intermediate-presheaf-kan.

I read the primary PDF online at https://www.math.ias.edu/~lurie/papers/HTT.pdf. There is no archived HTT copy in the named literature tree or listing. Accordingly proof_origin is agent, with the online document and explicit places, rather than claiming an archived source. These are infinity-categorical results with no Stacks tag. No SGA source is used.

## What needed repair or clarification

The item arrived unsplit, without proof steps or a Lean audit attachment. Its statement agrees with the source and is retained verbatim. Its general case is NOT obtained simply by using the entire larger-universe local presheaf category: that would enforce preservation of larger colimits which the stated target need not admit. I constructed the replete full closure of the localized generators under the original universe's colimits, and separately embedded each target by opposite Yoneda into a category with the needed larger colimits. The actual extension is shown to land back in the original target by that closure property.

The full functor-category equivalence also needs more than uniqueness on objects. Steps 6-7 construct a Kan comparison on the inverse-image intermediate presheaf subcategory, descend the comparison across the restricted reflector, and prove it is an equivalence by its equivalence locus. This accounts for all mapping spaces. The induction in steps 8-9 proves cocompleteness of both intermediate functor categories by pointwise colimits and writes the interchange argument. It does not assume a theorem on presentable targets, which would be too restrictive.

Naturality in the target is the usual naturality for colimit-preserving functors between cocomplete targets; arbitrary postcomposition need not even map the indicated full functor categories to one another. No statement text was changed. The source proof on p. 413 describes an inverse-image subcategory with three occurrences of “limits” although the construction, hypotheses and inference use colimits; I used the colimit-closure inference explicitly, not that word in isolation. This does not affect the theorem statement.

The item initially did not appear in the shared snapshot, but appeared during normal synchronization before I copied it. An early dry-run request eventually stopped at the missing-report gate; it was not an accepted delivery. No repository or launcher file was edited and no git, Lean, Lake, or compiler command was run by me.

## What remains unfinished

The two new supporting statements deliberately have no proofs and join the stage-1 queue. Their claims are proper supporting results, not rewritten clauses of the item: the first supplies presheaf accessibility, and the second supplies a mapping-space adjunction for arbitrary, possibly non-colimit-preserving functors on an arbitrary intermediate full subcategory. The item's relations, localized closure, multivariable extension, and presentability conclusion are proved in the item itself. No mathematical part of the assigned one-level split is left implicit as a future proof of the item.

## Not duplicates

lem-coef-infinity-presheaf-presentability vs lem-coef-space-presheaf-presentability: the existing statement assumes an ordinary category D and treats only its nerve; the new statement permits every small quasicategory, as required for C in the item. Replacing C by an ordinary homotopy category would lose its higher mapping spaces.

lem-coef-infinity-presheaf-presentability vs lem-coef-presheaf-local-presentability: the existing result is about ordinary functors into an ordinary locally presentable category; the new result is about coherent functors into spaces.

lem-coef-infinity-presheaf-presentability vs lem-coef-algebroid-segal-localization-model: the existing presheaf claim assumes a small monoidal infinity category and includes enriched localization/tensor claims depending on the tensor node above this item; C here is an arbitrary quasicategory, without a monoidal structure. It cannot be used as a general presheaf presentability theorem or as a circular foundation for this item.

lem-coef-infinity-intermediate-presheaf-kan vs lem-coef-infinity-presheaf-free-cocompletion: the existing equivalence restricts both source functors to colimit-preserving functors on the whole presheaf category. The new result computes maps to arbitrary functors G on E, with no colimit preservation and no colimit closure of E. That stronger-in-a-different-direction mapping property is what constructs the comparison to f L_E; it does not follow merely by taking the restriction equivalence's fully faithful subcategory.

lem-coef-infinity-intermediate-presheaf-kan vs lem-coef-infinity-kan-mapping-restriction: the existing node gives a mapping-space equivalence after a pointwise Kan colimit hypothesis; it does not assert that a colimit-preserving presheaf functor meets that hypothesis along the representables for every intermediate full E. The new node supplies precisely this presheaf-density implication.

lem-coef-infinity-intermediate-presheaf-kan vs lem-coef-infinity-relative-kan-existence: existence of lifts from given local relative cones does not identify the representable slice colimits or the required mapping-space restriction for the functor H; the new statement has different input and output.

Whole-DAG statement searches and blueprint_refs searches for cocompletion, presheaf presentability, Kan extensions, and the cited HTT numbers found no existing node covering either new statement. Both have inherited blueprint ancestry through the item with the exact coefficient-adjunction foundation place. No Stacks-tag duplicate pairs occur.

## Review by Q59

I read the worker brief, delivery-errors B-E in full, the three-level rule in SETUP, the stage-1 contract, GOAL, dag-sync, the chapter and bound unit, and the current blueprint ancestor's proof at main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md. Its second paragraph uses the coefficient mapping-complex adjunction before the derived inverse limit; this split stays in the inherited enriched tensor-cocontinuity foundation supporting that paragraph. The assigned node is not the unit's key statement, so no unit realization field is edited. I checked the primary HTT source cited above for the item and Remark 5.5.3.7 for the first new node. For the second I read the presheaf-density/left-Kan argument and the mapping-space adjunction in Proposition 4.3.2.17; I corrected its source page reference to pp. 284-285 and named that proposition rather than treating existence alone as the adjunction.

For C4 I opened the statement of every cited existing node. Here is what each step takes, and why the hypotheses suffice:

1. The new presheaf-presentability statement allows arbitrary small quasicategories in the chosen larger universe. lem-coef-presentable-infinity-adjoints explicitly supplies presentability of the small-arrow localization, the reflector, and its colimit computation. C and S really are small in that enlarged universe.
2. lem-coef-infinity-small-localization-saturation explicitly makes each S-arrow invertible under L. The localization-adjoint node supplies L's colimit formula. The intersection defining P and restriction to E are written out; the cone bases remain U-small even though the ambient presheaves use V.
3. lem-coef-infinity-yoneda-presheaf-limits states full faithfulness, representable limit preservation, and pointwise limits. Applied to Z opposite and W-spaces, these give the opposite Yoneda embedding and preservation/reflection of the needed colimits. lem-coef-infinity-full-essential-image supplies the coherent equivalence to the replete image, not an equality of unrelated categories. W is chosen large enough for Z and its mapping spaces.
4. lem-coef-infinity-presheaf-free-cocompletion is applied with C V-small and the larger target admitting V-small colimits, not to Z under an extra cocompleteness hypothesis. The saturation node states that every reflector unit is in the saturation, and the arrow operations inverted by H are each checked. lem-cbc-enhanced-functor-cone-calculus supplies pointwise detection of natural equivalences used in arrow-colimit inversion.
5. The localization-adjoint statement computes the colimit of a Q-diagram as L of the ambient colimit. The natural equivalence H eta identifies the comparison, and the full-essential-image statement permits factorization back into Z; the original U-colimit closure is exactly sufficient.
6. The new intermediate-presheaf-Kan statement applies to E containing y(C), even though G need preserve only U-colimits. It constructs the transformation on the whole mapping space. The existing free-presheaf node constructs H_f, and the cone-calculus node detects beta from its pointwise components. I wrote the descent across L_E using B eta, so no unquoted general localization universal-property lemma is used.
7. The new Kan statement gives the transformation-space equivalence, including arbitrary G, and full-essential-image gives the equivalence from a fully faithful restriction. The map is identified as restriction itself on generators.
8. The Yoneda/presheaf-limit node states the pointwise characterization conditional on the relevant colimits existing. Interchange is proved by the identical coherent family of maps in both orders. The only colimits requested in the possibly large functor source are U-small colimits in Z, which exist.
9. The same pointwise characterization translates the elementary exponential identity into the induction. The unary theorem used here has already been proved in steps 1-7; it is not a circular citation of the item. The induction starts at zero and one variables and step 8 checks both targets are cocomplete.
10. Composition of the actual restriction functors gives the compatibility. Mapping-space full faithfulness from previous steps identifies transformations and their parameter simplices, so no unsupported “transport of homotopies” is assumed.
11. The new general presheaf-presentability node and localization-adjoint statement apply in U when C,R are U-small. lem-coef-space-yoneda-density explicitly writes every presheaf as a small colimit of representables; applying L proves P equals Q. The existing ordinary-index presheaf-presentability node could not supply the first assertion for arbitrary C.

I declared cone calculus as a generic tool use because it is filed in another unit. It does not replace a step of the coefficient unit's proof. All other proof dependencies have the item's unit. Every citation has a verbatim statement quotation in citations.json, so the reader can check the claimed interface without consulting a dependency's proof.

For B and D I checked self-contained new statements, introduced every object and universe, supplied definition dependencies, single-escaped TeX, exact blueprint ancestry and searched same_as fields, unsplit statements with empty proof/proof_deps, and searches actually run through msearch.py with the exact query text. Both semantic phrasings, LeanSearch, Loogle and source grep succeeded; no unavailable service was reported as absence. The candidate Mathlib files were read at the lines named in the verdicts: ordinary Category/Type hypotheses rule out each specialization. Neither new node restates the relation-imposing completion or its multivariable clause.

For E I tested C empty, R empty, empty-base relations, an inconsistent-looking relation, and zero/one/two variables. For C empty, P(empty) is the terminal one-object category with its object initial, so the colimit-preserving functor category into Z is contractible, as is Fun(empty,Z). R empty gives the usual free completion (on large data only its U-colimit closure). For C a point and a specified empty-base cone to that point, localization forces the generator to be initial; the universal property selects exactly initial-valued functors. A relation identifying a non-colimiting cone causes no contradiction and j_R is not claimed fully faithful. The new Kan statement holds for E equal to the representables, where the restriction is the identity, and for E the entire presheaf category, where it is the standard Kan adjunction; H is initial-valued if D is empty, giving contractible maps to any G, so that edge also passes. The first new node at D empty gives the terminal presentable infinity category. The two-variable induction uses colimit interchange, not preservation of products by colimits.

The statement and coefficient categories are unchanged. This is a foundation lemma for arbitrary infinity categories, not a geometric base-change morphism, so it introduces no finite/adic coefficient identification or target hypothesis change. I checked the newly introduced dependency directions: neither support node points to the item or its descendants, and no bounded-colimit-presentation or tensor theorem above the item is cited. The required server review and final delivery dry run are run on this sandbox; it is handed over only after the dry run prints OK, with no push.

## Second reading by Q59

- Item statement: checked against HTT Propositions 5.3.6.2 and 5.3.6.11 and the small-data localization in Proposition 5.5.4.15, hypothesis by hypothesis; verdict correct.
- Step 1: checked the universe enlargement, presheaf presentability, and local reflector against the cited presheaf-presentability and presentable-adjoints statements; verdict supported.
- Step 2: checked the replete colimit closure, localization of each prescribed arrow, and the inverse-image subcategory against the saturation and adjoints statements; verdict supported, including empty bases.
- Step 3: checked opposite Yoneda, reflection of existing colimits, and the larger presheaf target against the Yoneda-limits and full-essential-image statements; verdict supported.
- Step 4: checked the free extension, inversion of the prescribed arrows, arrow-colimit closure, and localization units against the free-cocompletion, saturation, and cone-calculus statements; verdict supported.
- Step 5: checked descent through the reflector and the minimality argument against presentable-adjoints and full-essential-image; verdict supported.
- Step 6: checked the intermediate Kan comparison, explicit descent on transformations, and equivalence locus against the new Kan node, free-cocompletion, and cone-calculus statements; verdict supported.
- Step 7: checked all mapping-space identifications and restriction maps against the Kan and full-essential-image statements; verdict supported.
- Step 8: checked pointwise colimits and the two-order interchange argument against Yoneda-limits; verdict supported.
- Step 9: checked the zero/one-variable bases, induction target cocompleteness, exponential identity, and higher transformations; verdict supported.
- Step 10: checked compatibility as equality of restriction composites and mapping-space naturality from Steps 7 and 9; the short direct argument is elementary.
- Step 11: checked the small-data specialization, density by representables, and presentability model against presheaf-presentability, presentable-adjoints, and Yoneda-density; verdict supported.
- New node `lem-coef-infinity-presheaf-presentability`: checked self-containment, definitions, HTT Remark 5.5.3.7, Mathlib searches, and empty/point cases; verdict proper statement-only support node.
- New node `lem-coef-infinity-intermediate-presheaf-kan`: checked self-containment, definitions, HTT Lemmas 5.1.5.3/5.1.5.5 and Proposition 4.3.2.17, Mathlib searches, and representable/full-presheaf edge cases; verdict proper statement-only support node.
- No statement, proof, citation, or dependency repair was needed. I appended this second-reading record only; no Lean, compiler, Lake, or live-project files were touched.
