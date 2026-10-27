# Stage-1 delivery: lem-sf-integral-support-functor-normalization

## Files written

- dag/nodes/sec-smooth-purity/lem-sf-integral-support-functor-normalization.json: statement unchanged, split into seven steps; not a Mathlib leaf.
- citations.json: one verbatim statement quotation for every step/node citation.
- report.md: this report and signed review.

No new nodes and no Mathlib leaves. All writes are confined to this item's sandbox. The helper write_split.py is sandbox scratch material, not a project delivery file.

## Attachments

None. I searched lean/WeilConjectures for the blueprint tag, integral support, extension by zero, integral closed image and the relevant compact-support operations. CompactSupportIntegral.lean:100 defines Etale.rightDerivedLowerShriekDerivedCompleteIntegral using constant-ring etale modules; its exactness and linearity instances do not normalize the completed pro-etale ring-sheaf operation of this item. ClosedImmersionStages.lean:187 and following similarly treat the etale integral category and do not give every clause here. They do not justify an ATTACH.

## Wanted literature

None. The blueprint and the Stacks source used here are present. The proof is marked agent assembly, because the blueprint does not itself supply all these normalized ring-sheaf and system equations.

## Original item and route

The live item was unsplit, with no proof. There was no prior sandbox item, split, report or search log at the start, and no repair note. I read GOAL.md, the chapter and unit records, the current main-20261015 ancestor proof (the integral and rational paragraphs), and both B--E blocks of delivery-errors.md. The statement remains byte-for-byte unchanged. The unit record is the older snapshot; this is an auxiliary node, not the unit key node, so no unit file is changed.

The current ancestor is prop-sf-open-closed-triangle-all-stages, via lem-sf-rational-localization-triangle-orthogonality. I retained its precise from.place and searched blueprint_refs.py for integral support, extension zero, direct image limits, completion, extension-by-zero and closed immersion. I read the matching existing statements rather than creating clause-sized replacement nodes. In particular the existing open reduction theorem is stronger than the open comparison needed here, and the existing completed direct-image theorem supplies the canonical strict-limit comparison. No general Tor-amplitude assumption was added: the item's uniformly bounded reductions need not have uniformly finite Tor dimension over A_n.

## Searches and reuse

The item retains its original search records, and appends all five searches actually run by this worker from searches.jsonl (Loogle, two LeanFinder phrasings, grep and LeanSearch). Results were read. Loogle returns presheaf and sheaf pushforward adjunction infrastructure; LeanFinder returns algebraic adic-completion extension maps; LeanSearch returns scheme structure-sheaf restriction adjunctions; grep returns pro-etale-site and ell-adic cohomology definitions. ElladicCohomology.lean was read: it constructs the continuous-coefficient sheaf and its cohomology, not this support normalization. None is a match for the item's completed coefficient categories and its specified maps. The grep results differ from the older item record, so its new results are recorded as actually returned rather than replacing the historical record with an invented empty search.

Mathlib leaves already in the DAG are reused: lem-cbc-exact-linear-derived-functor is ExactFunctor.lean:122 (read lines 108--125); lem-sp-fully-faithful-adjunction-restriction is Adjunction/Restrict.lean:42,63,70,76 (read lines 26--88). No new Mathlib claim is made.

## Not duplicates

No new nodes. Existing open comparison, direct-image/limit normalization, ringed recollement, finite constructibility and full-subcategory adjunction nodes are cited directly.

## Review by Q17

I checked the statement and each proof step with the cited node statements open. The literature I read was: main-20261015 prop-sf-open-closed-triangle-all-stages.proof.md; sites-modules.tex Tags 03DI (lemma-extension-by-zero), 03DJ (lemma-extension-by-zero-exact), 0E8I (lemma-j-shriek-and-tensor); sites-cohomology.tex Tags 0GL1 (lemma-j-shriek-and-tensor), 0A07 (lemma-Rf-commutes-with-Rlim), 07A6 (lemma-adjoint); proetale.tex Tags 09AA (lemma-closed-immersion), 09BM (lemma-closed-immersion-complement-retrocompact-exact), 09BN (lemma-open-immersion), 09AG (lemma-jshriek-zero), 09AH (lemma-ses-associated-to-open), and 099N (lemma-pushforward-Noetherian-case); etale-cohomology.tex closed-immersion statements, and the existing blueprint lem-fin-closed-immersion.md. The item introduces no new statement-only node requiring an additional source review.

Step 1 uses integral-immersion-pullback-normalization for exactly its Noetherian/qcqs, finite perfect quotient, coefficient-map, exact restriction, shift and preservation conclusions. The ringed-open-closed node explicitly allows an arbitrary ring sheaf, gives exact j_! and i_*, and gives j^*i_*=0; it is not the finite-constant-coefficient adjunction proposition. The operation definition supplies the specified module adjunction. I checked quasi-compactness of j, which is essential for pro-etale closed exactness (09BM); it follows from the cited normalization in this Noetherian setting.

Step 2 uses integral-open-reduction-comparison for its actual r_j, completeness, unit inverse and system-realized adjunction maps. The compact-support definition supplies the tower for the identity proper factor. The formula is the actual unit formula, and the source of d_j is the specified J_R. This is not just a claim that their object values have some isomorphism. No assertion that evaluated maps are jointly faithful is made.

Step 3 uses direct-image-limits for canonical tower commutation, actual completion-unit normalization, finite projections, quotient transitions and completeness over the completed coefficient sheaf. The direct-image definition supplies the specified I_R tower. Commutation of scalar restriction with closed direct image is written out as the same section evaluation with the same induced action. Exactness from Step 1 permits termwise derivation, so this does not misuse the finite-to-finite restriction-of-scalars theorem for an infinite completed ring, nor assume scalar restriction preserves K-injectivity. The inverse comparison has the required direction I_R to ordinary i_*.

Step 4 uses open-finite-constructibility-interval for precisely its A_n coefficient rings and unchanged integer bounds. For the closed side I checked all four statements: constructible-origin provides G_n, finite-level comparison is exact, comparison-direct-image applies because the closed map is qcqs and G_n is bounded below, and fin-closed-immersion gives constructibility and vanishing of higher etale direct images. Exactness identifies cohomology termwise; no spectral-sequence lemma is hidden. The definition of the integral category then applies with the same [a,b]. I did not use adic-closed-direct-image-finiteness, whose statement is about Qbar_l sheaves and would not prove the needed A_n assertion.

Step 5 is one chain calculation of shift compatibility. The strict-Roos node supplies its normalized functor and augmentation with zero second component; the direct-image-limit node supplies the specified derived comparison of the underived limit equality, and the open-reduction node supplies the actual unit and r_j. Termwise shift changes the differential by (-1)^r, and each degreewise comparison commutes with this change. The same calculation on the signed cone gives the prescribed limit shift. In particular I did not invoke integral-basic-operation-shift or integral-realization-shift-coherence, since both impose finite Tor-amplitude hypotheses absent here. This step is 1293 characters, and all seven steps are below 2000 characters; no source-standard comparison is being left as an unexplained assertion.

Step 6 uses exact-functor-derived-triangulated for the termwise exact structures, integral-constructible-triangulated for full-subcategory closure and inherited triangles, the existing Mathlib exact-linear-derived leaf for linearity, and integral-constructible-linear for the actual constant-section scalar action. Underived linearity is checked directly on module maps; the displayed naturality equation and cancellation establish it for the specified functors. The exact structures agree because Step 5 proves the shift square, not because an unspecified isomorphism transports an arbitrarily chosen shift.

Step 7 uses the exact-derived-adjunction definition for the localized termwise units and counits (it defines those maps), and the full-faithful-adjunction-restriction Mathlib leaf for the actual Hom bijections, triangles, and unit/counit formulas. Preservation of both full subcategories was proved before applying it. The pullback normalization fixes the comparison functors, and open-reduction-comparison fixes agreement with strict-system realization. Finally ringed-open-closed gives j^*i_*=0, now applied termwise, so the final vanishing is elementary composition with the already fixed comparisons.

For edge cases I checked U=X,Z=empty and U=empty,Z=X: the maps are respectively the identity-operation completion comparisons and the unique zero functor comparisons. Zero input, arbitrary shift, n=1, equal-level transition, and nonreduced Z are covered without extra assumptions. In particular no reduction of Z or smoothness was silently assumed; closed exactness and comparison apply to closed subschemes as stated. The [a,b] argument is independent of n. I checked the transitive statement/proof dependency closure for every cited result and found no path back to this item.

Corrections made during review: avoided using constant-etale upstream constructions as an attachment; avoided the finite-field or Qbar_l closed-finiteness nodes for A_n; avoided the finite-to-finite scalar restriction theorem for B_T to A_n; and avoided shift results that assume finite Tor amplitude. No statement dispute remains and no statement change was made. Off-unit proof statements are declared as generic tool uses in split_report, for maintainer review; they do not replace the unit's open-closed route.

## Unfinished work

None in the one-level stage-1 split. Proof dependencies remain their own DAG tasks. The required server dry run and push are recorded by the delivery tool.
