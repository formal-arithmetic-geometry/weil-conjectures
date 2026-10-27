## Worker report

Item: lem-pur-closed-support-exceptional-mate. Group: Q99. Stage 1 only.

### Files written

- dag/nodes/sec-smooth-purity/lem-pur-closed-support-exceptional-mate.json: split into eight steps; Mathlib has the general adjunction formulas but no declaration of this complete supported-class and exceptional-mate assertion.
- citations.json: one verbatim statement quotation for every dependency of every proof step.
- report.md and searches.jsonl: report and genuine search records. write_split.py is sandbox scratch work, not a delivery file.

## New nodes

None. There are zero new Mathlib leaves. The existing finite-exchange and supported-Hom nodes already contain the non-elementary inputs; the four mate equations are proved in the item's own steps.

### Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for exceptionalBaseChange, closedSupport, supported adjuncts, and related counit calculations. FrameClass.lean's supportedTransport_comp_counit concerns two closed immersions with the same range in one scheme, rather than arbitrary Cartesian pullback. SupportCohomologyRestriction.lean also does not state all clauses of this item. No finished declaration of the complete item was found.

### Literature

No WANTED sources. Read the current main-20261015 thm-pur-affine-line-orientation.proof.md: the sentences on naturality of the supported Cartier map and final etale-origin comparison are precisely this item's place. Read the chapter and sk-prop-a1-kummer unit records and their coefficient and geometric-fibre qualifications. Read Milne, Lectures on Etale Cohomology, Theorem 9.4, the Ext discussion and Example 9.5 (printed pp. 65-67), and the closed-support right adjunction before Theorem 16.7 (printed pp. 111-112). Only that adjunction, not Milne's purity proof, is relevant here. Read Stacks categories.tex, Tag 0037, definition-adjoint and the following counit formula; etale-cohomology.tex, Tags 03QP and 0959, proposition-finite-higher-direct-image-zero and lemma-finite-pushforward-commutes-with-base-change. The relative coefficient, mate calculation, and site-transport assembly are explicitly agent-written. No SGA source is used.

### Statement clarification

The supplied statement referred to lem-pur-supported-hom for an etale Hom group. That node explicitly states a pro-etale result. I replaced that cross-reference with lem-pur-supported-hom-pullback and lem-amb-closed-support-hom, whose statements specify the ordinary etale identification, and added the latter statement dependency. No object, hypothesis, equation or conclusion was changed. The pro-etale result is still used through the full site-comparison clause of lem-pur-supported-hom-pullback. There was no false mathematical assertion requiring a weaker replacement.

### Searches and reuse

The sandbox was empty apart from dispatcher markers. I copied the current live item and preserved its inherited searches. All five additional searches were run through msearch.py with Q99 and this item: two distinct LeanFinder phrasings, Loogle CategoryTheory.Adjunction.homEquiv, the recorded grep pattern, and a LeanSearch phrasing. All services answered. The semantic hits concern structure-sheaf pullback or free modules, not this constant-coefficient supported assertion. Loogle finds the useful general counit formula; I read Mathlib/CategoryTheory/Adjunction/Basic.lean:160-182 and use the existing Mathlib leaf lem-weil-pbc-adjunction-of-natural-bijection, rather than introducing another node.

Searched all dag/nodes by titles and statements for finite exchange, closed immersions, counit mates, adjunctions, supported Hom and site comparison; opened every selected statement in full. Ran blueprint_refs.py ancestor and whole-blueprint searches for closed support, finite morphism, counit mate, adjunction, closed immersion finite, supported Hom, exceptional counit and finite exact. The more general existing sk-lem-pbc-finite supplies the exchange. lem-kun-base-change-open-closed needs a clopen immersion and is therefore unsuitable. lem-sf-ring-sheaf-base-change-mates has qcqs/pro-etale hypotheses not assumed here and is not used. lem-pur-exceptional-mate-site-comparison requires finite-type base changes and is not used for arbitrary geometric fibres. No new node was needed.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. In particular no node was created for any of the four equations, for exact inverse image, or for finite direct-image exchange.

## Review by Q99

I reread the item against the current blueprint and the printed Milne passages. The blueprint asks for naturality and etale-origin comparison, not purity of arbitrary base changes. The split retains that distinction: the invertible map is direct-image exchange b, while beta is merely its exceptional counit transpose. The elementary calculations are written in the item instead of moving its conclusions into new lemmas.

Step 1 uses the statements of lem-weil-pbc-closed-immersion-base-change and lem-weil-pbc-closed-immersion-finite to make i' closed and both direct images finite. sk-lem-pbc-finite explicitly gives exactness, arbitrary base change and the constant-coefficient derived exchange, not just a stalk formula for abelian sheaves. prop-weil-pbc-inverse-image-modules-exact explicitly identifies inverse image with constant-coefficient module pullback and states its exactness. The Mathlib leaf lem-sf-exact-functor-derived-triangulated supplies the shift comparisons. lem-exc-closed-ambient states the ordinary etale right adjoint for an arbitrary closed immersion. Only part (1) of lem-pur-exact-derived-adjunction-bounds is used, with its exact left adjoint hypothesis now checked. lem-weil-pbc-adjunction-shift-compatibility-unique states the compatible shifted counit, so writing Ri!F[a] causes no hidden typing change. None of these applications imposes finite type on h or X'.

Step 2 uses precisely the inverse Hom formula in lem-weil-pbc-adjunction-of-natural-bijection, first for u and then for beta. It yields the first and third equations by their definitions. Step 3 uses the natural finite exchange of sk-lem-pbc-finite at the particular morphism u. I checked the direction: b_K h*(i_*u)=i'_*g*u c, so the needed equation uses b_K inverse on the left and c inverse on the right. Step 4 substitutes the third equation into the second and uses bijectivity of the same Hom formula. These steps need only functoriality, associativity, naturality and inverse cancellation; no exceptional base-change isomorphism is smuggled in.

Step 5 uses the actual displayed etale equation of lem-pur-supported-hom-pullback, with exactly h, i, F, a and alpha as in this item. Its statement includes arbitrary h and X', constant coefficient modules, the shift comparison and the canonical c. It says what this step takes; the pro-etale-only lem-pur-supported-hom cannot be substituted here. That was the cross-reference I corrected.

Step 6 applies exact site inverse image using the full statement of lem-sf-comparison-pullback-exact and the derived exact-functor leaf. prop-weil-pbc-comparison-direct-image requires a qcqs morphism, not qcqs schemes. The closed immersions satisfy this: finiteness includes affineness (def-weil-finite-integral-morphism), and lem-weil-pbc-affine-morphism-permanence explicitly states qcqs. Thus no condition on the open complement or on the arbitrary fibre was added. lem-weil-pbc-comparison-pullback states natural inverse-image comparison on arbitrary schemes. The equations on this side are images of etale equations with their endpoints compared, not equations justified by an ambient pro-etale exceptional adjunction.

Step 7 writes the actual arrow on the pulled-back adjunct: C(beta) C(g*u). Naturality of k_g identifies this with g_proet*(C(u)) followed by C(beta) k_g inverse. The supported-Hom-pullback statement explicitly includes the pro-etale identity, its compatibility with the etale identity under nu*, and commutation with h* and c, so it supplies the class identification as well. The named right adjoint object at an arbitrary geometric fibre remains C(Ri'!h*F[a]).

Step 8 checks the only finite-type use. A closed immersion uses the compactification with identity open part; its ordinary etale compact-support functor is its exact direct image. The finite formula in def-weil-exceptional-inverse-image is exactly C_Z i! Rnu_X,* after this choice. thm-weil-pbc-site-comparison supplies its unit isomorphism for every bounded-below constant-finite-coefficient object, without constructibility. Full faithfulness and the step-6 direct-image comparison give the transported Hom bijection and hence the same counit transpose. For a geometric fibre outside the definition's finite-type domain, the argument uses the ordinary closed adjoint already supplied in step 1, instead of pretending the restricted definition applies there.

Small cases checked: identity h gives b=1 and beta=1 by the counit transpose; identity i makes the assertion ordinary functoriality; empty Z gives zero supported object and zero maps; zero F or alpha makes each equation zero; negative a only changes the canonical shifts. The same arguments allow a non-finite-type geometric base change. No regularity, smoothness, purity, finite Tor dimension or constructibility hypothesis was used. These tests also show why a proof demanding invertibility of beta would be inappropriate.

I checked B-E point by point with the cited statements open: no new statement-only leaf was needed; all cited non-elementary inputs are existing statements; no proof body is used as if it were a statement; no duplicate, clopen-only exchange, or finite-type-only mate theorem was substituted. The long-step check finds no step over 2000 characters. A dependency traversal found no path from any chosen dependency back to this item. The ordinary etale finite-exchange and comparison tools from other units are explained in split_report.tool_uses as generic tools; the Kummer route is unchanged. Nothing remains mathematically unfinished in this one-level split; the required server preflight and delivery follow.
