# Stage-1 report: lem-sf-roos-adjunction-unit-coherence

## Files written

- dag/nodes/sec-six-functors/lem-sf-roos-adjunction-unit-coherence.json: item, statement; split into four explicit elementary calculations using existing normalized comparison statements. No statement or statement-dependency change.
- citations.json: seven step/node entries, all checked as verbatim substrings of the cited statements.
- searches.jsonl: six actual searches made with the prescribed msearch.py command (two LeanFinder phrasings, Loogle, LeanSearch, two grep queries). The item's inherited search records are retained and these searches appended.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches under lean/WeilConjectures for the exact blueprint tag and for Roos/adjunction/unit/product comparisons found no project declaration stating this whole item. Existing project RoosComplex and comparison files concern tower resolutions and homotopy comparisons, not the two-functor normalized adjunction-unit identity. The related Sheaf/SixFunctors/OpenExchangeRoosRestriction.lean and OpenRoosUnitAdjunction.lean contain sorry and concern the open-immersion specialization; they are not attachments.

## WANTED

None. All sources used are present locally.

## Corrections and scope

The item previously had a statement and searches but no proof. Its statement is retained. The underlying source Stacks Tag 0941 supplies the derived-limit/Roos route; it does not state this two-functor unit coherence. The proof is therefore honestly marked agent-written. I read Tags 09BN and 09BP as motivation for the open adjunction and preservation assumptions, and do not use their scheme-specific conclusions to infer anything for arbitrary functors in this item. No SGA source is used.

The existing normalized strict-limit comparison already carries the hard comparison construction, its specified conjugation formula and augmentation compatibility. A new node for any of those facts would duplicate it. Conversely, the new calculations are projection naturality and cancellation of specified isomorphisms, so extracting them as new nodes would make elementary or clause-restating nodes. No statement dispute, change of unit route, or new literature request is needed.

## Not duplicates

There are no new nodes and hence no new/existing same-tag pairs. The existing lem-cbc-exact-product-functor-strict-limit is used for each functor separately; it is not the item because it does not give the compatibility between two functors and a specified adjunction unit. lem-sf-open-roos-restriction-unit specializes the sought conclusion to open extension/restriction and has extra coefficient data, so citing it would neither prove the general item nor remove the need for the general calculation. The unrelated lem-trf-isomorphism-roos-unit-cancellation concerns a scheme isomorphism and quotient/Koszul augmentation and is not used.

## Review by Q87

I read the worker brief, stage-1 contract, SETUP's three levels and tool-lemma rule, GOAL.md, and delivery-errors B through E, including the repeated B--E sections. I read the six-functors chapter and sk-prop-sf-pf-coherence unit, and the current-main-20261015 proof paragraph for prop-sf-pf-coherence. This item refines its open-factor sentence that both maps restrict to the identity. It does not replace the unit's route or edit its chapter/unit record.

For the source I read sites-cohomology.tex, lemma-derived-limit-is-ok (Tag 0941), including its K-injective normalization and short exact product sequence, and proetale.tex, lemma-open-immersion (09BN) and lemma-j-shriek-limits (09BP), including their proofs. The two-functor identity is an explicit formal refinement, not attributed to Stacks as a verbatim theorem. There are no new node sources to audit.

For Step 1, I checked the directions of both product comparisons. The nth projection of their composite with u is GF(pr_n) u, which is u_n pr_n by the naturality axiom. Product uniqueness proves precisely the asserted map. This needs no external lemma beyond the universal property defining a product, so its empty uses list is intentional.

For Step 2, I opened and read the full statements of lem-cbc-exact-product-functor-strict-limit and lem-weil-strict-roos-comparison. The former explicitly says kappa is phi on both signed summands; the latter supplies the strict-square Roos functor. Composing with either signed projection and then any tower projection gives GF(r)u = u r. These projections jointly determine each component of the map. I checked transitions and differentials: unit naturality makes u_M a strict tower chain map; in the second differential coordinate, naturality intertwines 1-s and the differential, with the same minus sign on both sides. The statement's signed model has x in degree q and y in q-1 throughout. This calculation is elementary relative to the two cited results and hides no comparison theorem.

For Step 3, I reread the actual displayed lambda = theta^{-1} kappa F(theta) formula in lem-cbc-exact-product-functor-strict-limit and the natural-isomorphism assertion of lem-weil-strict-roos-comparison. Both hypotheses hold twice: A and B are small-site module categories, both have exact countable products, and F and G are exact additive functors with invertible canonical comparisons, all explicitly assumed by the item. I also read def-weil-exact-derived-adjunction: it says exactly that the derived unit is the localized original unit. Thus the unit naturality equation is available on the derived morphism theta, even though theta need not be an honest chain isomorphism. In the expansion the intermediate G(theta_FM) cancels its inverse; Step 2 then gives H(u_M); naturality of theta converts it into L(u_M). Only after this conversion do I use invertibility of u to cancel L(u_M^{-1}). This preserves the specified normalization and does not invoke uniqueness of a cone filler.

For Step 4, I read the whole strict-augmentation clause of lem-weil-strict-roos-comparison: the representative is (gamma,0) and corresponds to the actual derived augmentation. I also read the last paragraph of lem-cbc-exact-product-functor-strict-limit, which says the same lambda preserves that actual augmented map. Postcomposition with H(u_M) gives (u_n gamma_n,0); naturality on gamma_n gives (GF(gamma_n),0) after u_C. I checked that the second coordinate stays zero in both degrees and that the source unit is actually present. Unit coordinates mean composing each target coordinate with the inverse component of u; this yields the claimed identities and does not assert an unnormalized comparison is literally identity between different objects.

I tested small cases: F=G=id with the identity adjunction gives identity at every stage; a zero tower or zero augmentation keeps both components zero; a constant tower with identity transitions has 1-s as prescribed and the same formulas; towers with zero transitions and arbitrary unbounded differentials still satisfy the coordinate calculation. A nontrivial scalar automorphism u=a id for the identity functors on modules (with inverse scalar counit) gives a on both Roos summands and a^{-1}a=1 in the derived cancellation. This checks that the argument genuinely uses the specified unit and does not silently replace it with identity. No boundedness, injectivity preservation by F, or geometric condition is used.

For Mathlib I read piComparison and piComparison_comp_π in CategoryTheory/Limits/Shapes/Products.lean (lines 651 and 655), and derivedη and derivedη_fac_app in CategoryTheory/Functor/Derived/Adjunction.lean (lines 96 and 103). Searches returned derived-unit normalization and binary-product comparison lemmas; neither gives the whole item's signed Roos and derived-limit compatibility including augmentations in one specialization. No entire-item Mathlib match was found. Blueprint searches for Roos, adjunction unit, normalized product and signed Roos found no imported node giving the same statement. Existing general comparison lemmas were reused.

C1/C4: every non-elementary input is one of the cited existing comparison statements; citations.json quotes only their actual statements. B1--B9/D1--D5: no new nodes, no definition or hidden lemma manufactured, no proof moved out of this item. E1--E7: source/target categories and functor order are fixed in each equation; the only inverse needed additionally is the unit already assumed invertible. Each proof step is below 900 characters, so there is no long step concealing a lemma. Cross-unit normalized Roos and exact-functor comparisons are declared as generic tool uses in split_report; they supply no alternative route for a unit theorem.

## Unfinished work

None for this one-level split. Its existing comparison dependencies retain their own independent proof obligations in the DAG. No Lean was written or compiled, and the repository and launcher files were only read. The required server dry run and direct delivery follow this report.
