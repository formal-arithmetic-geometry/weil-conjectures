## Worker report

Group Q112; stage 1; item lem-sfb-properness-normal-curve-local-test.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-properness-normal-curve-local-test.json: the unchanged statement, now split in six steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-normal-curve-universal-closedness-test.json: one new statement-only, unsplit node for Stacks 0GWV, equivalence of universal closedness, closedness after every affine-space product, and existence of the restricted local lifts. Mathlib verdict: no match.
- citations.json: 28 entries, one exact statement quotation for every step/node pair.
- searches.jsonl: the recorded real searches; the searches completed before the launcher pause were retained and read. One further item phrasing was completed after resumption.

No Lean, compiler, Lake, direct git command, or other agent was used. The only writes were to the specified sandbox. No unit realization field changes are appropriate: the item is a tool below the unit, not its key statement.

### Attachments

None. I searched lean/WeilConjectures for the item's blueprint tag, normal-curve properness, and the essentially-finite-type properness criterion. No project declaration states the item. The search hits for general valuative criteria are Mathlib declarations, not project attachments. Existing closed/Mathlib nodes are reused rather than recreated: in particular the normal dimension-one DVR theorem, proper valuative extension, and local-finite-type cancellation.

### Literature wanted

None for this delivery. The necessary Stacks source is present locally. The inherited blueprint ancestry includes historical WANTED text; it is preserved, and none of those unavailable books is used in this split.

### Audit and changes

The item agrees with limits.tex Tag 0GWX, label lemma-essentially-finite-type-criterion-proper. Its condition is restricted to diagrams from C and U=C minus c. I did not replace it by a criterion quantifying over all maps from fraction fields. No statement correction or STATEMENT-DISPUTED is needed. In particular X and Y can be nonreduced, and neither must be globally quasi-compact or separated. The hypotheses are local finite type over an arbitrary field and quasi-compactness of f.

I followed 0GWX and the diagonal argument of 0GWW (lemma-essentially-finite-type-criterion-separation). Instead of adding a new separatedness criterion, I proved its relevant argument: the two projections of a map C to X times_Y X restrict to two local lifts of the original square. The item's uniqueness identifies them and gives a lift to the diagonal. This uses local uniqueness directly, so it does not require the additional global gluing result 0GWT. The single new lemma is used twice, for f and for its diagonal; it is the independent universal-closedness test of 0GWV, not the original properness theorem with a new name. The item's proof supplies the separatedness argument, the finiteness hypotheses for the diagonal, and the forward implication.

The current latest blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). It now assembles direct images through compactification. This inherited branch supplies a generic properness tool below that assembly; no unit or chapter route was changed. tools/blueprint_refs.py ancestor reports None for this item's inherited chain. I retained its existing from.node=null, prepended the item to the new node's via list, and supplied an exact supporting place. Whole-blueprint searches for 0GWV, universally closed, normal curves, and curve properness found no node stating the restricted criterion. DAG searches by tag and concept found only the current item for 0GWX and no existing 0GWV criterion.

### Mathlib searches

The item's existing searches remain intact. The new searches and verdicts are copied from actual Q112 searches.jsonl records with identical tool and query strings. For the new node I used LeanSearch, LeanFinder with two semantic phrasings, Loogle, and grep restricted to Mathlib/AlgebraicGeometry. These services succeeded. The returned hits are general universal-closedness definitions and permanence results, or UniversallyClosed.of_valuativeCriterion. Reading Mathlib/AlgebraicGeometry/ValuativeCriterion.lean at lines 231-241 shows that this last theorem needs all valuation-ring squares; it does not specialize in one line to the finite-type-curve test. Reading lines 330-345 similarly rules out treating IsProper.of_valuativeCriterion as a leaf for the item. FiniteType.lean:72 does give cancellation, but the existing lemma-nagata-finite-type-to-separated-target already states it, so the provisional searches for a cancellation leaf produced no new node. Provisional separatedness searches also produced no new node.

### Remaining work

The new 0GWV node is deliberately statement-only and joins the stage-1 queue. Nothing in the item's six-step assembly remains unspecified. The independent maintainer review will judge this delivery after the required preflight and push.

## Not duplicates

lem-sfb-normal-curve-universal-closedness-test vs lem-sfb-properness-normal-curve-local-test: the former characterizes universal closedness by existence alone and also states the affine-space closed-map test; it allows nonseparated g. The latter characterizes properness by unique local lifts. Its uniqueness-to-separatedness proof remains in the item, through the diagonal, and is not moved to the new node.

lem-sfb-normal-curve-universal-closedness-test vs lemma-nagata-proper-separated-valuation-extension: the latter starts with properness and supplies unique lifts for all valuation rings; it does not deduce universal closedness from restricted curve diagrams.

lem-sfb-normal-curve-universal-closedness-test vs lemma-nagata-proper-valuative-criterion-existence-api: the latter supplies lifts from proper morphisms for arbitrary valuation rings; it does not state the restricted converse or affine-space closedness test.

The following four pairs share only the ancillary reference 0335 (fields are Nagata), not 0GWV. I opened each statement:

lem-sfb-normal-curve-universal-closedness-test vs lem-sbc-normal-finite-stage-universal: this existing node constructs a finite normal approximation stage with a mapping property; it has no curve-local closedness criterion.

lem-sfb-normal-curve-universal-closedness-test vs lem-sbc-normal-finite-stage-diagram: this existing node constructs a whole diagram of finite normal approximation stages; it has no criterion for universal closedness of a given morphism.

lem-sfb-normal-curve-universal-closedness-test vs lem-weil-pbc-finite-type-field-integral-closure-finite: this existing node asserts module finiteness of integral closure in a finite field extension, not existence of local lifts or any morphism closedness criterion.

lem-sfb-normal-curve-universal-closedness-test vs lem-weil-pbc-finite-type-z-domain-normalization-finite: this existing node asserts finite normalization of a domain of finite type over Z, not the field-relative test in 0GWV.

## Review by Q112

I read the item against the actual enumerated statement and proof of limits.tex 0GWX, and the new node against all three conditions and the proof of 0GWV. Both source lemmas assume a Nagata base. For this specialization I checked algebra.tex 0335, proposition-ubiquity-nagata, item (1), which explicitly includes fields. Normality in both statements means normal integral local rings, as specified by def-weil-pbc-normal-ring; the dimensional condition is on O_(C,c), and c is required to be closed. No perfectness, algebraic closedness, or separateness of C is introduced. Condition (2) of the new node has all n including zero; its products are over k and its polynomial ring is the actual multivariable polynomial ring defined by the cited definition node. The canonical spectrum-of-stalk map is explicitly named. The new node contains no proof sketch or deferred data construction, and has empty proof and proof_deps and null proof_origin and mathlib_match.

Step 1 uses the actual clause (a) of lemma-nagata-finite-type-to-separated-target: the composite alone being locally finite type suffices, with no separatedness of p_Y. The definition of finite type supplies the combination with the given quasi-compactness. I read pqf-def-locnoeth and pqf-lem-locnoeth-lft: they give exactly local Noetherianity, not global Noetherianity. The base is locally Noetherian because a field has only two ideals. This also verifies the same hypothesis when C is used in step 2.

Step 2 uses the Noetherian affine chart promised by pqf-def-locnoeth; the canonical-local-ring node explicitly identifies the stalk with A_p. I checked the localization-noetherian statement, which permits exactly this localization. I read algebra.tex 00PD, lemma-characterize-dvr, conditions (1), (2), and (5), and checked the existing lem-sc-normal-dim1-dvr and def-sc-discrete-valuation-ring statements: normal, Noetherian, local, domain, and dimension one all hold here. The existing proper-separated valuation-extension node supplies existence AND uniqueness; it is not the existence-only API. Properness supplies separatedness from the definition, and the equation over Y forces k-linearity. The precise stalk-localization and valuation-extension quotations are in citations.json.

Step 3 uses exactly implication (3) to (1) of the new 0GWV statement. The diagrams and the fraction field are identical to the item's; only uniqueness is forgotten. This is not an application of Mathlib's unrestricted valuative criterion to a smaller test family.

Step 4 uses the local-finite-type base-change node for p_1 and clause (e) of proper-fp-permanence for its composition with p_X. Cancellation applied to p_1 after delta (the identity) supplies local finite type of delta, without assuming f separated. The locally-noetherian-quasi-separated node states exactly the needed compactness of intersections of affine opens of X; it is not used to assert global compactness of X. The affine-spectrum fibre-product node makes A times_V B affine. The open inclusions and their inverse images are checked by the fibre-product universal property. During my self-review I corrected an imprecise reference to an 'affine-cover test in the definition': the definition does not itself state target locality. I added lem-pc-quasi-compact-local-on-target and wrote the elementary intervening calculation. A finite affine cover of the compact source makes inverse images of basic opens finite unions of compact principal opens, by the actual statements of basic-open-pullback, spec-localization-away-basic-open, and affine-scheme-qcqs. Compact affine opens in the target have finite basic-open covers. Thus the restricted maps themselves are quasi-compact, which is precisely the hypothesis of the local-on-target node. The monomorphism calculation is just cancellation by the explicit left inverse p_1. No separate lemma is hidden in this finite-cover calculation.

Step 5 is the substantive uniqueness argument. I checked the new 0GWV statement can be applied to delta: X and P are locally finite type over k, and delta is quasi-compact by step 4. Its two maps b_i are defined on all of C and have the same restriction a on U. Therefore their restrictions to Spec R are lifts for the SAME original square, with bottom map v=fb_1=fb_2, and the given uniqueness applies. The equal pair is a map through the diagonal by the stated fibre-product universal property. No factorization was inferred merely from containment of underlying point sets, and no equality of maps was inferred just from generic agreement. The local-lift formulation is why global gluing is unnecessary.

Step 6 uses the scheme-monomorphism-separated theorem (schemes.tex 01L4), with the monomorphism already proved, and the definition of properness, with all three properties of delta verified. The proper-monomorphism-closed statement is the exact iff from etale.tex 04XV; it gives a closed immersion, not just closed image. The definition of separatedness now gives separated f and its other two properness clauses were verified separately. I read all cited node statements, not their proofs, and citations.json copies their actual formulas or sentences. The canonical-stalk node is an off-unit foundational tool; it is declared in split_report.tool_uses. The other cross-unit inputs are already Mathlib leaves or closed results.

For B1-B9/C5 I checked the one new node is self-contained, statement-only, with the same notions as the item plus explicitly defined affine space and the canonical local map. The tag and label are correct, the TeX is escaped once in the decoded strings, no definition cites the wrong notion, and no new Mathlib leaf is asserted. Whole-DAG/blueprint/source searches precede its creation, and the same-tag pairs are explained above. C1/C3/C4 were checked by reading every statement quoted for each step, including clause (e) rather than the finite-type-only composition node initially considered. D1/D2 are addressed by retaining the full diagonal argument in steps 4-6: the original unique-lift conclusion is not delegated to another new node. The new universal-closedness lemma is strictly weaker and is applied to a second morphism. No proof step is over 2000 characters; there is no long inline comparison or source-standard subclaim left without its argument or a citation. The only new dependency points toward foundations and has no dependency back to the item.

For section E I tested the new criterion and assembly on: the empty source (all three conditions hold, with no map from the nonempty punctured integral test curve); the identity; the closed immersion Spec(k[e]/e^2) to itself; the nonproper open immersion G_m into A^1, where C=A^1, c=0, and u on G_m do not extend locally; and A^1 to Spec k, where u=1/t on the same punctured curve has no local extension. For existence versus uniqueness, the doubled-origin line over A^1 is nonseparated and universally closed (after every base change it is the union of two copies of that base, and a closed subset has image the finite union of its closed restrictions); it has existence but two lifts for the test curve at the origin. Thus the new node does not silently assert uniqueness, and the diagonal proof is needed. These checks work in arbitrary characteristic and require no reduction of X or Y. A zero-dimensional C has no allowed c of local dimension one, exactly as in the source, so it creates no extra test. Neither completeness nor excellence of a DVR is assumed anywhere.

The pre-report server review_split check passed. Full dry run and direct delivery follow this review; their actual outcomes are recorded below after they finish.

### Validation result

The required full dry run exited successfully: `OK (not pushed) deliver/Q112/lem-sfb-properness-normal-curve-local-test at 4916f5417ce: preflight passed`. This includes the server checks. The final proof steps have lengths 651, 900, 355, 1661, 891, and 471 characters. The push is made with the same delivery command after that process exited; its final result is reported by the worker on return.
