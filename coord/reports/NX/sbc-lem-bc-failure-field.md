# Stage-1 worker report: sbc-lem-bc-failure-field

## Files written

- dag/nodes/sec-smooth-base-change/sbc-lem-bc-failure-field.json: statement, split into eight steps; Mathlib has no field-detection theorem in the searches run.
- dag/units/sk-lem-failure-field.json: only realized and realized_by fields changed.
- citations.json: a verbatim statement quote for every citation in every numbered proof step.

No new nodes and no new Mathlib leaves. All supporting nodes already exist. Searches for the auxiliary qcqs fact located Mathlib instances, but the more general existing lem-weil-pbc-qcqs-morphism-permanence already supplies it, so no duplicate leaf was created.

## Attachments

None for the item. AlgebraicGeometry.Etale.nonempty_fieldFailure_of_not_universalBaseChangeProperty in WeilConjectures/SixFunctors/Etale/SmoothBaseChange/FailureOverField/Detection.lean:135 has a sorry-free body, but calls nonempty_fieldFailure, which calls isQcqsLocalProperty_survivesBaseChange. The latter uses three sorried survival declarations in Survival.lean:130, 144 and 162. It is therefore not a finished proof. FieldFailure.isAffineHom_a at FieldFailure.lean:99 proves only the final clause.

## WANTED

None. Tag 0F07 and the supporting Stacks source are available locally.

## Corrections and discrepancies

The imported proof mixed a source proof with descriptions of later Lean implementations; some cited facts were not attached to the step taking them. I replaced it with a single coherent argument, retained the statement, and added the base-change-map statement dependency. The imported statement leaves h and g unlabelled in its display; the proof fixes them as the projections and field structural morphism, respectively. Its q'≤q−1 phrase is understood in the nonnegative domain of the cited property definition. No change of mathematical hypotheses was made.

The blueprint already strengthens the wording of the Stacks single symbol BC to universal cumulative degreewise BC, correctly matching the definition and the use in the open summand. The proof does not assume j_* exact. The module-category Lean theorem has integer degrees and an arbitrary commutative coefficient ring, while this item uses n-torsion abelian sheaves, equivalently Z/nZ-module sheaves. I specialized the argument to that coefficient ring and did not silently equate arbitrary coefficient categories. Negative higher-image degrees are zero and hence impose no additional requirement.

Nothing remains unfinished in this one-level split. Existing unsplit supporting lemmas remain their own future items.

## Not duplicates

No new nodes. Before deciding this I searched the whole blueprint for 0F07, failure, morphism from, and quasi-compact quasi-separated, and searched the DAG by statement concepts and candidate Mathlib names. The auxiliary qcqs statement is already contained in lem-weil-pbc-qcqs-morphism-permanence, clauses (1)–(3).

## Review by NX

I read literature/stacks-project/etale-cohomology.tex, Tag 0F07, label lemma-base-change-does-not-hold-pre, including the actual closed–open and Leray paragraphs, and the chapter and sk-lem-failure-field unit. I read the item blueprint and the source Lean Detection, FieldFailure and Survival files. The Stacks proof first restricts to an affine base, then applies 0F06 to survival of a fixed stalk element; the split follows precisely that route. There are no new-node sources to review.

For step 1 I opened sbc-def-base-change-property, sbc-lem-etale-locality and lem-weil-pbc-qcqs-morphism-permanence: the first quantifies preliminary base changes, the second clause (3) tests the same degreewise maps on the induced etale cover, and permanence supplies both preservation under localization and absolute qcqs of T. I retained the distinction between a qcqs morphism and a qcqs scheme. All later U→S' satisfy the morphism assumptions because S' is affine and U is qcqs.

For step 2 I opened all four cited statements: injectivity clause (1) gives a monomorphism from universal degree q−1; geometric-stalk exactness preserves it, stalk conservativity detects the failed isomorphism, and the canonical-stalk definition introduces the actual source, target and transition maps. An injective non-bijective group map has an element outside its image. I fixed the coefficient ring to Z/nZ throughout.

For step 3 I checked that the source thickening lemma asserts a source isomorphism and that the target thickening lemma requires the Cartesian square that our fibre construction provides. Transport composition states exactly r_i(t_V ξ)=t_U ξ. The needed commuting square is spelled out via the unit/counit mate formula and naturality, rather than attributed to the site-equivalence definition. Surjectivity of the source comparison and injectivity of the target comparison prove both directions of image membership.

For step 4 I opened source-image-limit-descent, target-limit-zero-detection, target-stalk-restriction-image and stalk-transport-composition. The first descends a source image, not a nonzero class; the second kills the difference after one finite transition, not merely at the limit; the third preserves the base-change range; the fourth transports the original element to that stage. The subtraction argument uses exactly these statements. I checked their affine-base, small-cofiltered, qcqs-stage and affine-transition hypotheses. In particular this does not infer persistence of non-membership merely from a formal colimit equality.

For step 5 I checked the coefficient embedding, open-injective-zero and closed-coefficient-range statements verbatim. The open comparison needs membership after restriction to V and vanishes in the open injective target; the closed comparison needs membership after restriction to Z and puts the closed coefficient image into its range. Neither statement asserts the whole field-detection conclusion. The previous-degree universal hypotheses persist for p and its further base changes. Empty V or Z cause no exception: the zero summand satisfies the same range assertions.

For step 6 I checked injectivity clause (2), which injects cokernels under coefficient embeddings, and stalk exactness, which preserves that injection and identifies cokernel stalks. The algebraic reconstruction from two projections is written using the biproduct identities and naturality of the same base-change map. This corrects the imported text's compressed passage from summand information back to survival.

For step 7 I checked all four hypotheses in the statement of sbc-lem-bc-minimal-counterexample, including the empty-scheme condition, and wrote the empty-site argument. The conclusion supplies a field morphism to T, and the composite to S' gives precisely the required fibre square. The coefficient remains n-torsion under inverse image. For q=1 the open comparison uses only degree zero; there is no hidden higher-degree assumption. For n=1 all coefficients are zero, so the failure hypothesis cannot hold; likewise empty X has no failed stalk. These cases are consistent with the statement.

For step 8 I opened the separatedness definition, fibre-product definition, closed-immersion affine-chart characterization and affine-morphism definition. The inverse image over an affine W is a closed subscheme of Spec(A⊗_Z B), hence is a quotient spectrum; this gives the asserted affine morphism without adding separatedness of the initial auxiliary base. I checked the argument also for empty affine charts. These off-unit definitions and generic tools are declared in split_report.tool_uses; no unit proof step was replaced by an unrelated route.

I checked B–E point by point: no new-node shape, search, or duplicate defects arise; every cited use has its literal statement quote; elementary portions are explicit algebra or definitions; the limit and coefficient comparisons are genuinely cited lemmas, not source tags masquerading as dependencies; no proof is moved into a new clause node. The delivery dry run below is the remaining mechanical gate.

## Statement corrected

Citation metadata only: removed the unstable version-dependent number “Lemma 59.88.6” from the parenthetical Stacks citation, retaining Tag 0F07 and every mathematical word and formula. The source field is maintainer-owned, so the worker cannot add the number there. Two dry runs identified that inherited citation mismatch; the correction removes it without changing the proposition.


## Earlier second reading (a previous round; superseded)

- Step 1: checked Tag 0F07 (lemma-base-change-does-not-hold-pre), the universal-property definition, etale-locality clause (3), and qcqs permanence clauses (1)–(3); PASS, including absolute qcqs of T only after affine localization.
- Step 2: checked injectivity clause (1), exactness and conservativity of geometric stalks, and the canonical transition definition; PASS, with the initial canonical square and coefficient ring fixed throughout.
- Step 3: checked both thickening transition statements and transport composition; PASS, with the mate naturality calculation supplying the commuting square and the two isomorphisms giving both directions of image membership.
- Step 4: checked source-image descent, target zero detection, image preservation and transport composition; PASS, with affine base, small cofiltered indexing, qcqs stages and affine transitions all present. The difference element is killed at a finite stage, which supplies the contradiction.
- Step 5: checked coefficient embedding, open-injective zero, and closed-coefficient range verbatim against the closed–open paragraphs of 0F07; PASS. No exactness of open direct image is used; all lower nonnegative degrees, including degree zero, are available.
- Step 6: checked injectivity clause (2) and stalk exactness; PASS. The displayed biproduct identities and coefficient naturality reconstruct the zero cokernel class without assuming that either summand detects the whole theorem.
- Step 7: checked all four hypotheses and conclusion of the minimal-counterexample node; PASS. The empty-site argument proves the extra empty condition explicitly. For n=1, zero coefficients or empty X there is no failed map; q=1 consumes precisely degree zero in step 5. Field and empty closed/open pieces cause no exceptional case.
- Step 8: checked separatedness, the fibre-product universal property, the quotient-spectrum characterization and affine-morphism definition; REPAIRED two uncited geometric facts. Read lem-pc-closed-subscheme-base-change-ideal-image against Schemes Tag 01JU, label lemma-fibre-product-immersion, and lem-weil-pbc-fibre-product-affine-spectra against Tag 01I4, label lemma-fibre-product-affine-schemes. Both apply without added hypotheses; neither has a dependency path back to the item. The step is now non-elementary and explicitly cites them.
- New nodes: NONE; all supporting nodes pre-exist, so there is no new-node form, duplication or Mathlib-leaf claim to validate. The two added citations reuse general existing statements rather than introduce special cases.

Changes and reasons:

1. STATEMENT-DISPUTED: the imported display and preceding text did not bind g or h, although the conclusion contains R^q g_* and R^q h_*. As written these functors have no specified domain. Bound g to the field structural map and h,e to the fibre-product projections, exactly as in the labelled diagram of Tag 0F07. Wrote 0≤q'≤q−1 explicitly, matching the nonnegative domain of sbc-def-base-change-property. This repairs notation and typing without adding hypotheses or weakening the conclusion; all existing uses keep their meaning.
2. Added the two existing geometric statements to step 8, its proof dependencies and verbatim citations; marked the step non-elementary. Declared the off-unit closed-immersion result only in split_report.tool_uses for maintainer review, as SETUP.md authorizes; the affine-spectra result is already a Mathlib leaf. Their general statements are the facts actually needed by the final clause, not alternative routes for field detection.
3. Retained the first worker's report and Review by NX verbatim. Its statement-retention and elementary-final-step remarks describe the original delivery; this second-reading section records the final repairs. The earlier ## Statement corrected section is supplemented by the binding/domain repair recorded here.

The slopmaster2 Detection.lean and Survival.lean were read independently: the detection wrapper reaches the three survival sorries, so it is not a finished-proof attachment. No Lean file was written and no compiler or build tool was run.

Validation: deliver.py NX sbc-lem-bc-failure-field --no-push printed `OK (not pushed) deliver/NX/sbc-lem-bc-failure-field at e77db2ea8c: preflight passed`. The normal delivery reruns the same gate before pushing.

## Rebase repair (2026-10-14)

The landing was refused because the reviewed citation quote for `sbc-lem-etale-locality` contained the former parenthetical `Lemma 59.86.1`, while the current DAG statement retains the same three clauses but now says `Lemma [Tag 0EZR]`. I re-read the current node and replaced every corresponding entry in `citations.json` with its exact current statement text. No proof step or dependency changed; the quotation now matches the rebased node verbatim.

I also re-read the local Stacks source, `etale-cohomology.tex`, label `lemma-base-change-local` (Tag 0EZR), including its proof of restriction compatibility, and `lemma-base-change-does-not-hold-pre` (Tag 0F07). The current locality clause (3) still gives exactly the degree-q implication used in step 1. I made its application explicit: V_i are affine opens of S_1 and U_i=X_1×_{S_1}V_i; these are an etale covering of X_1, both structural open immersions are etale, and the displayed squares and coefficient restrictions coincide with those in the current statement. Thus if all restrictions were isomorphisms, clause (3) would force the original map to be an isomorphism. The contrapositive still supplies the required failing affine restriction. No changed hypothesis requires a different route.

I revalidated all 29 quotation entries against the current DAG statements; every quote is a verbatim substring. The reported changed statement differs from the earlier quoted statement solely by removal of the version-dependent lemma number, not by a mathematical clause. All other citation quotes remain valid. The dry run with supported syntax `deliver.py NX sbc-lem-bc-failure-field --no-push` passed at `6513aebec5`; the final dry run below additionally checks the explicit hypothesis expansion in step 1. Nothing was pushed.

## Second reading by NX

Item statement: compared with 0F07 (lemma-base-change-does-not-hold-pre), 0F02 (remark-base-change-holds), and the blueprint item/unit. PASS on the project coefficient domain: the existing definition restricts n to positive integers invertible on S, whereas Stacks allows any integer. The cumulative universal lower-degree hypothesis is precisely Stacks BC(f,n,q−1) on this domain; failure in degree q follows because all lower degrees already hold. The field, two Cartesian squares, coefficient and failed map agree with the labelled source diagram. Affineness of S' is supplied by its proof; the separated-base affine-morphism clause is the explicit blueprint addition proved in step 8. The earlier STATEMENT-DISPUTED binding repair correctly defines g,h,e without changing those hypotheses or maps.

- Step 1: read 0F07 (lemma-base-change-does-not-hold-pre), 0EZR (lemma-base-change-local), locality clause (3), the universal-property definition and qcqs permanence clauses (1)–(3); PASS. The affine opens cover after pullback, and absolute qcqs follows only after localizing the base.
- Step 2: read injectivity clause (1), exact geometric stalks, stalk conservativity and canonical stalk transitions; PASS. An injective failed stalk has an element outside its range, with the initial square canonical.
- Step 3: read both thickening-transition statements, the base-change mate definition, the module transition definition and transport composition; REPAIRED. The source and target isomorphisms apply to the Cartesian fibre square; the displayed transpose calculation now proves compatibility by counit naturality and the triangular identity, before passing to cohomology and stalks.
- Step 4: read source-image-limit-descent, target-limit-zero-detection, restriction-image and transport-composition statements against the limit paragraph of 0F07; PASS. Descend the source image, subtract the transported element, kill the difference at a finite stage and obtain the forbidden stage image. Affine base, small cofiltered index, qcqs stages and affine transitions are present.
- Step 5: read closed-open coefficient embedding, open-injective-coefficient-zero and closed-coefficient-range against the closed–open paragraphs of 0F07; PASS. The coefficient is Z/nZ, the lower universal degrees include zero, and the open complement is quasi-compact; no exactness of open pushforward is assumed.
- Step 6: read injectivity clause (2), exact stalks and coefficient naturality of the mate; PASS. The biproduct identities reconstruct a zero class for G, and the injected cokernel forces a zero original class.
- Step 7: read all four conditions of the minimal-counterexample node and the conclusion against 0F06 (lemma-formal-argument) and 0F07; PASS. The empty-site argument supplies the extra empty condition; pullback keeps n-torsion, and the field stalk failure implies map failure. At q=1 only degree zero is used in the open comparison; n=1, zero coefficients and empty X cannot satisfy the failure premise. Empty closed/open pieces cause no exception.
- Step 8: read the separatedness, fibre-product, closed-immersion and affine-morphism definitions and the closed-base-change and affine-spectra statements; PASS. The diagonal pullback is closed in Spec(A tensor_Z B), so each affine-open preimage is a quotient spectrum. No separatedness of the preliminary base or nonemptiness of its affine charts is required.
- New nodes: NONE; there is no new statement to test or search, no new Mathlib leaf to verify, and no node to remove for B1–B7 or duplication. All tools are existing nodes.

Changes and reasons:

1. Replaced step 3's compressed instruction to expand and cancel adjunction maps with the two explicit transposes and their equality. This removes the remaining E5 gap and identifies the functors and coefficient where naturality is applied.
2. Cited the existing def-sbc-module-higher-image-transitions for the unit transition formula, added its proof dependency and a verbatim statement quote. This repairs C1 without a new node. All other steps and the corrected statement were retained.
3. Checked all original 29 quotes against the current DAG; each was verbatim. The added quote is the full current transition definition. The first worker's Review by NX and all previous report sections remain in place.

Independent source reading: local Stacks etale-cohomology.tex at the three labels above, the blueprint item and unit, and read-only slopmaster2 Detection.lean and Survival.lean. Detection reaches the three survival sorries, so its wrapper is not a finished proof. No Lean files, compilers, Lake or build tools were used.
