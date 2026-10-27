# NX stage-1 delivery: lem-pur-adic-source-finiteness-reductions

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-adic-source-finiteness-reductions.json: statement, split; eight proof steps using existing nodes; Mathlib searches give no match.
- citations.json: one literal statement quotation per step/node citation.
- report.md: this report. No new nodes or Mathlib leaves.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and adic/source terminology. Read WeilConjectures/EtaleCohomology/Purity/Smooth/Adic.lean, especially exists_iso_realization_twistShiftPullbackLevel. It assumes supplied normalized source and target systems and level identifications; it proves neither the actual source finiteness nor the required canonical reduction comparisons. It is not an attachment.

## WANTED

None.

## Corrections and scope

The statement is retained in full. The imported node had no proof; its source only says that the bounds and stratifications are those of K with the same dimension shift. The split now handles the support interval separately from the Tor interval, identifies the specifically defined source arrow rather than merely an isomorphism between endpoints, and writes the direct quotient and triple quotient equations. The common bounds required here are supplied by the definitions of integral constructibility and integral finite Tor amplitude. This item asserts constructibility and common intervals, not an additional universal choice of stratification.

I initially considered lemma-weil-pbc-completed-pullback-reduction, then read its intrinsic-completion hypothesis against def-weil-derived-complete. The latter is the Roos-triangle condition; silently substituting it would be an unjustified change of completeness conventions. I removed that citation and use the coherent finite-system calculus and normalized-DVR effectivity on the actual defining pulled tower. No statement dispute or change to the unit route is necessary.

Nothing mathematical remains unfinished in this one-level split. Auxiliary results are existing DAG statements, not claimed newly proved here. Only stage 1 was performed; no Lean writing, compiler, Lake or build command was used, and all authored files are in the assigned sandbox.

## Not duplicates

No new nodes. Blueprint searches for pullback, twist preserves, pullback reduction and finiteness reductions, and the whole-DAG statement/title searches, led to the existing pullback, finite-Tor, line and coherent-system results cited by the proof.

## Review by NX

I read the current main-20261015 thm-pur-adic-reconstruction proof and the chapter and sk-thm-purity-transport unit, including Step 2. Its intended route realizes the normalized finite source system; the proof stays below that step. I also read Bhatt--Scholze pp. 22--24 and 49--51: Definition 3.4.10, Lemma 3.4.12, Proposition 3.5.1, Definitions 3.5.2--3.5.3 and Lemma 6.5.9 explain the quotient-limit completed operations and finite-system convention. I read Stacks proetale.tex lemma-pushforward-Noetherian-case (099N), and sites-cohomology.tex lemma-pullback-tensor-product (07A4). These are source checks, not uncited black-box proof steps. No SGA source was used. There are no new nodes requiring separate source audits.

For Step 1 I opened def-weil-finite-tor-amplitude, lem-sf-pullback-tor-amplitude, prop-weil-pbc-proetale-constant-exact and lem-weil-pbc-exact-functor-complex-cohomology. The first supplies a uniform Tor interval for all K_n, the second preserves that interval at finite coefficient stage, and the last two provide exact inverse image and its actual cohomology isomorphism. This avoids inferring the independent support interval from a Tor bound. All schemes and f satisfy the stated finite-type and separated hypotheses; ell is invertible because the base characteristic differs from ell.

For Step 2 I read prop-weil-twist-preserves: it explicitly preserves constructibility and every support/Tor interval at finite coefficients. The signed cohomology formula for a shift moves each endpoint down by 2d. Tensoring a degree-zero test module commutes with this shift, giving the Tor statement with the same sign.

For Step 3 I read lem-pur-integral-operations-preserve-constructible for M and the canonical reduction isomorphisms, def-weil-pbc-adic-coefficient-datum for the normalized input tower, and lem-coef-semilinear-derived-sections for exact inverse image of whole systems and its scalar-extension comparison. The pulled system is normalized because this comparison carries each input normalization isomorphism to the corresponding output isomorphism. The actual M is its derived limit by def-pur-integral-derived-operations. The statement of lem-coef-normalized-dvr-effectivity gives coherent canonical counits for this system without constructibility or boundedness assumptions. I read lem-pur-integral-operation-roos-effectivity, which explicitly identifies the finite comparisons with adjuncts of the actual projections even after transport through the defining model. Thus this step proves the normalization for the particular pullback maps used later. It does not identify the constant and completed coefficient categories, and does not invoke the differently defined intrinsic-completion predicate.

For Step 4 I read lem-pur-twist-sheaf-locally-free for the completed rank-one line and all finite models. Lem-pur-integral-line-reduction-restriction applies with precisely those hypotheses and M complete and constructible. Its statement gives the completion comparison, completeness and reductions. Lem-pur-integral-line-derived-comparisons additionally gives the actual K-flat/counit and strict-transition normalization. Def-pur-adic-twist-reduction fixes the scalar-adjunct definition with quotient actions retained. These are cited for their statements, not their proofs.

For Step 5 I read def-pur-adic-source-reduction, def-pur-adic-finite-tensor-realization and def-pur-adic-root-comparisons. Their order of composition and pure-root tensor equations agree with the constructed composite. Lem-weil-derived-scalar-extension-restriction-adjunction states a bijection on the relevant derived Hom sets; equality is checked on its prescribed transpose and normalized K-flat representative, rather than inferred from merely having isomorphic endpoints. This verifies the assertion about the actual b^U_n.

For Step 6 I rechecked the coherent counit assertion of lem-coef-normalized-dvr-effectivity, the strict transition formulas of lem-pur-integral-line-derived-comparisons, and the root normalization of def-pur-adic-root-comparisons. Lem-sfb-successive-derived-quotient-normalization supplies the balancing formula, unit compatibility and naturality for arbitrary composable maps of ring sheaves; it imposes no flatness on quotient maps. This proves the displayed direct-quotient square for all b >= a, including successive quotients. Every action remains over its specified finite coefficient sheaf.

For Step 7 I read the actual normalization formulas and cocycle in def-weil-pbc-adic-coefficient-datum and the iterated-comparison assertion of lem-sfb-successive-derived-quotient-normalization. The proof writes the two triple-balancing formulas explicitly and substitutes the already proved squares. This elementary pasting proves units and cocycles; it does not assume evaluation detects equality of arbitrary derived-system maps. Step 8 uses exactly the shift closure stated in lem-weil-integral-constructible-triangulated and the uniform reduction condition in def-weil-finite-tor-amplitude to conclude integral ctf membership.

I checked delivery-errors B--E: there are no new statement-only nodes, duplicates, relabelled clauses, Mathlib matches without source lines, or uncited facts quoted by tag. All non-elementary inputs have existing statement nodes; citations.json copies their statements literally. Every proof step is shorter than 2000 characters. The generic tools from other units are declared individually in split_report.tool_uses; they supply finiteness, scalar adjunction, coherent-system and line facts, and do not replace the unit's reconstruction route.

Edge cases checked: d=0 makes the twist/shift calculation the unit case; f the identity gives the canonical reduction system; K=0 and an empty X have vacuous support and Tor conditions; n=1 uses no nonexistent level zero; equal quotient indices give the unitor; three unequal indices give the written multiplicative cocycle; a ramified coefficient extension needs no divisibility assumption because all maps are the actual varpi-quotients, never a replacement by ell-powers. No flatness of A_b -> A_a is assumed. There is no new statement to test for false small cases.

The preliminary server review_split check passed before the completeness-hypothesis repair. The required full delivery dry run and final push follow this report.
