# Stage-1 delivery: lem-sfb-projective-line-invertible-classification

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-projective-line-invertible-classification.json: statement, split; no Mathlib match. Four steps, 2975 characters in total, none exceeding 2000 characters.
- citations.json: fourteen verbatim quotations, one for every cited node in every proof step, checked against the current statement strings.
- report.md: this report. searches.jsonl is the unmodified search-command log.

No new nodes; zero Mathlib leaves added. The item statement and its statement dependencies are unchanged. At the original split there was no earlier sandbox split or report and no repair note for this item. This repair retains that split, the report, the citations, and the search log.

## Attachments

None. Searched the project Lean source for the exact blueprint tag and for invertible/projective and classification/twist notions. Read ProjectiveSpace/LineTwist.lean: AlgebraicGeometry.ProjectiveLine.TwistData.existsUnique_iso compares two already supplied framed twists of the same integer. It does not assert that an arbitrary invertible module admits such frames, or that the integer is unique. The existence theorem there constructs the standard twist and is likewise only a partial input, not an attachment for this item.

## WANTED

None. All sources used are present in literature/.

## Corrections and scope

No statement dispute, source correction, or route change was needed. The source is divisors.tex, Tag 0BXJ, label lemma-Pic-projective-space-UFD, specialized only to n=1 and a field. I read its proof together with the preceding affine-UFD lemma, the existing blueprint affine-line algebra proof, and Sheaves Tag 04TN (lemma-glue-maps). The source's triple-intersection argument has no distinct triple for P^1; here its constant transition factor is removed explicitly by rescaling just the U_0 frame. The integer is d=-n because the project uses g_0=t^{-d}g_1. The source's classification is not made into another node or treated as a black box.

I read the chapter and the inherited sk-thm-sf-ctf-stability unit. This item is an algebraic tool deep below the inherited exceptional-fibre/alteration argument, not the unit's key theorem. Its blueprint ancestor is absent (the ancestor tool reports None); its existing from.node=null, inherited place, and via chain are retained. No chapter or unit file is modified. Whole-blueprint searches for projective line, Picard group, Laurent, and glueing morphisms, and DAG searches for 0BXJ and its label, found inputs and the parent, not an existing general classification over every field. The off-unit algebra and map-gluing results are declared as tool uses in split_report.

## Mathlib searches

The seven searches run for this item are appended with their exact tool and query strings to mathlib_searches, retaining the prior item's recorded searches. The command log records successful LeanFinder, Loogle, LeanSearch, and grep calls. Both semantic phrasings were read. CommRing.Pic.mk_eq_mk_iff and CommRing.Pic.subsingleton_iff (PicardGroup.lean, lines 486 and 528) concern modules over one ring; reading the surrounding source confirms that they do not classify projective-space sheaves. The alternative semantic search returns Proj structure sheaves and affine-chart isomorphisms. The scoped AlgebraicGeometry grep finds only Weierstrass comments on affine Picard groups. The initial broad grep produced irrelevant occurrences of invertible, so it was followed by the scoped grep and a direct reading of the ring Picard candidates. None is an exact match or a one-line specialization for this item. No unavailable service is recorded as a negative search.

## Not duplicates

There are no new node pairs to justify. The existing lem-pur-affine-punctured-line-algebra is reused for triviality of Pic(A^1_k) and the affine/Laurent unit formulas; lem-weil-pbc-glue-sheaves-of-modules is reused for gluing O-linear maps. Neither classifies invertible sheaves on P^1. The parent lem-sfb-projective-line-twist-rigidity consumes this classification and is never cited by this proof, avoiding a cycle.

## Review by Q119

I checked the split against B through E of delivery-errors.md with the current sources and cited node statements open. No new statement-only node is needed: all substantive facts already exist, and the proof itself carries the normalization, gluing compatibility, and uniqueness calculation. All fields other than the stage-1 split/search fields are retained; no Lean or compiler command was used.

Step 1 uses exactly the affine charts of def-sc-p1-standard and the invertibility definition to restrict L to the two charts. The current statement of lem-pur-affine-punctured-line-algebra explicitly says Pic(A^1_k)=0 for an arbitrary field. I read def-sc-picard-group: this is the group of isomorphism classes of invertible modules with unit O, so zero Picard class supplies the two module isomorphisms. The chosen frames are the images of 1, with the all-smaller-opens characterization stated by def-sc-local-free-generator. No algebraic closedness or extra cohomology comparison is assumed.

Step 2 uses the same free-generator definition to write e_0=u e_1 and e_1=v e_0 and cancel a generator, proving uv=1. The cited affine-punctured-line node states the Laurent unit formula used here; its reference to the small etale unit sheaf does not change this calculation, because its global sections on the terminal scheme are precisely global regular units. I verified the exact normalization a^{-1}e_0=t^n e_1 and the sign d=-n. This does not invoke any N-power assertion or any characteristic condition from the additional clauses of that node.

Step 3 uses the actual relation g_0=t^{-d}g_1 in def-sc-p1-standard and the free-generator definition to construct the local maps and their inverses on every smaller open. I checked the cited map-gluing statement: part (1), not a definition of gluing or only an object-descent theorem, gives existence and uniqueness of O-linear maps with these restrictions. Both directions have the same overlap identity, so both glue; uniqueness makes their composites identities. The proof does not merely say that the objects are transported or identified.

Step 4 uses the affine-line unit clause of the same algebra node, now on U_0 and U_1 separately, to make the two coefficients nonzero constants. I checked the compatibility equation b_0 t^{-e}=b_1 t^{-d}, yielding t^{e-d}=b_0/b_1. The current Laurent-polynomial definition explicitly includes uniqueness of coefficients. For a nonzero exponent its coefficient is 1 on the monomial and 0 on a constant, forcing e=d. The comparison of two isomorphisms for L is just their composition. Thus uniqueness concerns only the integer and does not falsely require a unique unframed isomorphism.

Edge cases checked: d=0 gives transition 1; d=1 and d=-1 agree with the stated sign convention; negative Laurent exponents are covered by coefficient uniqueness; arbitrary finite, real, imperfect, or positive-characteristic fields satisfy exactly the cited hypotheses, including k=F_2 where the coefficient contradiction still uses 1!=0. Different nonzero constant rescalings of an isomorphism are allowed. I checked that no non-elementary assertion is left as an uncited source tag, no cited statement is used only through its proof, and no step exceeds the long-step threshold. The assembly is under 3000 characters and creates no restatement of a clause of the item.

## Unfinished work

None in this stage-1 split. The existing input nodes remain the responsibility of their own DAG items. Delivery checks and push are run with the required launcher command.

## Dry-run repairs

The first dry run rejected four citations solely because their exact formulas were shorter than the gate's 40-character minimum. I expanded those quotations to the whole relevant statement and rechecked them verbatim. No proof or statement change was needed.

## Repair of the returned delivery (2026-10-23)

The return says the reader approved the mathematics but landing refused the side-project completion because it had not been promoted into the live DAG read by the queue. I did not treat the earlier completion as live completion. The retained dry-run receipt named head 0df37bcc8e7. I first ran the required dry run on the retained files; it exited successfully. I then compared the retained item with the current repository node: the current node is unsplit, its statement, statement dependencies, source, chapter, unit, origin and blueprint fields agree with the retained copy, and the differing fields are exactly proof, proof_deps, proof_origin, status, mathlib_searches and split_report. I rebuilt the sandbox node from the current node plus those retained stage-1 fields, updated the split report for this return, and clarified that the affine-line input is applied separately with coordinates t and s. The delivery tool fetches origin/sheaf-dag and builds the delivery on that current base; promotion into the queue's live DAG remains the maintainer's landing action.

For this repair I reread every input, including unchanged ones: def-weil-field gives 1 != 0; def-sc-p1-standard gives the two charts, their overlap and g_0=t^{-d}g_1; def-sc-invertible-module gives Zariski local rank-one triviality; lem-pur-affine-punctured-line-algebra still states Pic(A^1_k)=0 and the constant/monomial unit formulas over every field; def-sc-picard-group makes Picard equality equality of isomorphism classes; def-sc-local-free-generator gives bijectivity on every smaller open; lem-weil-pbc-glue-sheaves-of-modules part (1) still gives existence and uniqueness of O-linear maps, not just gluing objects; def-weil-laurent-polynomial-ring still includes uniqueness of Laurent coefficients. Neither of the updated blueprint statements attached to the field/Picard definitions changes a clause used here. All fourteen retained citation quotations remain verbatim in these current statements. Thus no dependency replacement or new node is needed.

I reread divisors.tex at lemma-Pic-projective-space-UFD (0BXJ), including its cocycle proof, and sheaves.tex at lemma-glue-maps (04TN); both tag/label pairs are confirmed by the current tags file. Steps 1 and 2 apply the algebra statement only to the two affine lines and their Laurent overlap, with no algebraic-closedness or power-surjectivity assumption. Step 3 uses the gluing theorem on the underlying Zariski ringed space with the displayed linear overlap identity in both directions. Step 4 uses only constant chart units and coefficient uniqueness, so fields of characteristic two and negative or zero twist degrees remain covered. The inverse composites restrict to identities and uniqueness in the gluing statement proves they are identities globally. These checks reconfirm C1/C4 and E1/E4/E5; no unproved subclaim, new-node relabelling, cycle, or route replacement is introduced (B, C5-C8, D). No proof step exceeds 2000 characters.

I also repeated the project declaration search and read LineTwist.existsUnique_iso: it still assumes framed twists of the same degree and does not classify an arbitrary invertible module. The Mathlib statement/search question did not change, so I read and reused searches.jsonl and the existing recorded results, and reread the CommRing.Pic candidates rather than repeating or inventing searches. No Lean file, repository file, launcher file, compiler, Lake command, or agent was used for writing/building this repair. The only edited files are the sandbox item and this report.
