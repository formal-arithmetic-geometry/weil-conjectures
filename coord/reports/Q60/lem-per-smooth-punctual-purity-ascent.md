# Q60: lem-per-smooth-punctual-purity-ascent

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-smooth-punctual-purity-ascent.json: statement item, fresh five-step split; Mathlib has no cohomological purity match.
- citations.json: one literal statement quote for every step/node citation (whole statements retained so no formula is truncated).
- report.md, searches.jsonl: review and actual search evidence. write_split.py is a sandbox-only assembly aid.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and punctual-purity concepts. The hits concern Frobenius weights, not local cohomological purity; the recorded removed Sheaf module is not a living theorem. No Lean file was written or compiled.

## Sources and searches

Read ILO, Travaux de Gabber, Expose XVI, printed pp.244--245 (Definitions 3.2.1--3.2.2, Proposition 3.2.3 and 3.2.5) and pp.248--249 (Propositions 3.5.2, 3.5.5 and Corollary 3.5.6). The preserved source states precisely this smooth ascent. Its surrounding trait-relative-class argument is not used as a black box: that older interface has stronger hypotheses and remains excluded. The proof is marked agent reconstruction. Instead, apply the same two-of-three argument to the closed fibre over the localized point of X, using smooth base change as in 3.5.2 and the admitted local version of 3.2.5. The finite-coefficient proof never uses a smooth trace or an arbitrary-field adic-duality assertion.

Read the current latest blueprint's chapter and sk-p-dl-a1-perverse section and the corresponding DAG chapter/unit records. This item is a historical auxiliary input rather than the unit's key node: their realized fields must not be changed. Preserve its complete historical blueprint provenance, including from.place and via; do not restore the discarded ancestor's proof. Blueprint searches for punctual, punctually pure, and smooth.*purity found no imported node stating this cohomological smooth-ascent assertion. The source graph already contains all the required ingredients, so no duplicate alias was created.

Retained all nine historical Mathlib search records after reading their results. Actual new msearch.py calls are in searches.jsonl: LeanFinder on punctual cohomological smooth ascent and then on the Kummer closed-point isomorphism; Loogle on "Etale", "purity"; grep on punctual/cohomological/absolute purity and Gysin; LeanSearch on smooth pullback preserving local etale purity. The returned smoothness, stalk and cotangent declarations do not assert local cohomological purity. The grep hits are only finestTopologySingle. No service failure has been described as mathematical absence.

WANTED: none.

## Repair and scope

Read coord/repair-notes/lem-per-smooth-punctual-purity-ascent.json and the Q91 route decision, plus the N0, Q84 and Q112 boundary decisions. The sandbox contained no previous item/report/searches when this attempt started, only old brief marker files. Copied the preserved current item and kept its statement, source, stmt_deps, historical searches, blueprint fields and lean_removed unchanged. The released repair overrides the obsolete proof approvals. None of the twenty direct proof inputs is listed in coord/route-pivot-dropped.txt. In particular, cite the admitted lem-per-trait-test-prime-field-local-input rather than the excluded lem-per-prime-field-punctual-purity; derive the short smooth support comparison from localization triangles rather than cite the excluded lem-per-regular-supported-base-change. No excluded interface is duplicated under a new id.

## Review by Q60

I checked B--E of coord/delivery-errors.md, both copies, with the cited node statements open. There are no new nodes whose self-containedness, tag provenance or splitting status could be confused with a proof. Every non-elementary input is an existing cited statement; proof_deps is exactly the union of the step uses. The citation file copies actual statement text, not a source paragraph or a node's proof. All five steps are marked non-elementary and are shorter than 2000 characters. The proof argues the conclusion rather than moving smooth ascent into another node.

Step 1 uses smooth restriction and the affine smooth-ring equivalence to put a compatible affine chart over a regular ring, then the regular-ring smooth-ascent statement to prove Y regular. The localization-base-change statement identifies B tensor C_p with the localization of B at C minus p. Localizing once more at the prime of y gives B_q, since every inverted element is already outside q. This is the local ring of Y, not a residue fibre ring; the eventual purity assertion is therefore about exactly the requested point and dimension.

Step 2 uses the ring smooth-base-change statement twice, over R and its residue field, and regular smooth ascent to obtain regular Noetherian V and F. The definition of regular local ring supplies d maximal-ideal generators, and the regular-generator lemma states that these form a regular sequence. Smooth-flat supplies flatness. The definition of a flat module explicitly preserves each multiplication injection after tensoring, so this small argument needs no additional flat-regular-sequence node. At a point of the fibre all parameters lie in its maximal ideal, ensuring the quotient is proper. The number d of the equations is unchanged; the flat pullback is the regular closed immersion to which the cited class-calculus base-change clause applies.

Step 3 uses the actual closed-support triangle, not a definition of flatness or of exceptional inverse image, to identify the two support terms. Exact inverse image and its triangulated extension preserve the first triangle. Bounded derived smooth base change applies to the constant degree-zero F_ell sheaf on the open complement. The base is affine Noetherian, hence the open immersion is qcqs; no smallness or constructibility hypothesis on an unbounded support object is being slipped in. The closed stalk and off-support vanishing statements identify the closed pushforward exchange; the conservative-stalk statement detects its isomorphism. The maps in the triangles are the canonical unit/counit maps as stated in the support-triangle node. The triangle two-isomorphism statement now gives the first comparison. Checking closed stalks again detects its invertibility on F. This is a routine comparison of two triangles from cited statements, not a separate hidden regular-base-change theorem or an arbitrary choice of a cone isomorphism.

Step 4 uses the hypothesis of punctual purity at x, exactly the local closed-point map a_i. The regular-immersion class-calculus statement explicitly gives flat base change, localization and twist compatibility and the Kummer sign, so it identifies the pulled-back class with the class of i'. The previous step proved the comparison invertible. This checks the map itself, not merely an abstract isomorphism between its endpoints.

Step 5 applies the admitted prime-field-local input to each O_F,z. These are regular Noetherian local rings with invertible ell and contain the prime field of the field k; that input expressly requires neither excellence nor finite type over the prime field. Its conclusion is exactly the local Kummer map needed for F to be punctually pure. The two-of-three statement applies to the regular closed immersion F into V with constant equation length d. Its conditions (a) and (b) yield (c), purity along F, which suffices for the chosen point v. The localization identification and class localization clause identify this with purity at y in the original Y.

I tested the empty source (vacuous), d=0 at a generic base point (empty regular sequence and identity closed immersion), smooth relative dimension zero (the same fibre argument), a positive-dimensional fibre and nonclosed y (never assume y is closed in the fibre), mixed characteristic and an imperfect residue field. The local prime-field input has no perfectness hypothesis. The proof does not require X or Y separated, since it uses only compatible affine charts. No completion regularity, excellence, global ample sheaf or extra trait hypothesis was added. No statement dispute was found. The preserved trait hypotheses are stronger than this local argument needs, which is harmless: the item statement remains unchanged.

## Not duplicates

No new nodes. Existing broad interfaces were searched and read instead of duplicated. No same-tag new/existing pairs occur.

## Unfinished work

No mathematical obligation remains in this one-level split; the cited unsplit interfaces remain normal separate stage-1 work. Await the required server dry run and delivery result below.
