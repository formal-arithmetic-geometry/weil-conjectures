# Stage-1 delivery: lem-sf-middle-exchange-projection-base-change

## Files written

- dag/nodes/sec-six-functors/lem-sf-middle-exchange-projection-base-change.json: existing statement item, now split into four steps; Mathlib searches found no match.
- citations.json: literal statement excerpts for all six step/node citation pairs.
- searches.jsonl: five actual searches performed through the mandated msearch command.

No new nodes; no new Mathlib leaves. The item statement, statement dependencies, original source fields and blueprint provenance are retained. The latest blueprint is the proof source used for this split.

## Attachments

None. Searched the entire project WeilConjectures source by blueprint id and by exchange/projection/base-change terminology. The closest declaration is AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap in SixFunctors/Etale/Derived/LowerShriekProjectionExchange.lean:160. I read its type and proof: it supplies the projection-formula square for finite module coefficients, not the present middle composite, not the additional exchange-pasting equation, and not all the item's coefficient stages. It therefore is not an exact attachment. The Kunneth/Relative.lean declarations likewise do not state the required identity.

## Wanted sources

None. I read the current blueprint proof of lem-sf-kunneth-coherence, the unit and chapter records, the current prop-sf-pf-coherence proof, and the current fix-lem-exchanges proof (the latter is in sec-six-functors-basics/sk-prop-sf-cbc in the latest blueprint). I also read Stacks Tag 07A4, sites-cohomology.tex, label lemma-pullback-tensor-product, for the natural tensor-pullback comparison. No forbidden SGA route is used.

## Problems and corrections

The seed item had a precise statement but no argument. No statement dispute was found. The split makes explicit the two factorizations of the same base map, the pullback-composition identifications c and r, the PF square at q, the naturality in c, and the final tensor calculation. No new hypothesis is introduced. The previously recorded searches are retained and the five new actual searches are appended, with their real hit names and no-match verdicts. Two LeanFinder phrasings returned scheme pullback identities or ordinary sheafification naturality; LeanSearch returned categorical pullback/pushout pasting; Loogle and the CategoryTheory grep had no hits. None gives the derived compact-support composite identity.

## Not duplicates

No new nodes were created. The whole-DAG and whole-blueprint searches for middle exchange, projection/base change and pasting found the existing ingredients. In particular prop-sf-pf-coherence already supplies the PF square; fix-lem-exchanges already supplies both horizontal pasting and naturality in square data; lem-pur-derived-pullback-tensor-iso already supplies the natural monoidal comparison. lem-sf-relative-product-base-change-factor-squares states larger factor squares and was not used to replace this item's argument. The parent lem-sf-kunneth-coherence was not cited, avoiding circularity.

## Review by Q95

I checked the split against delivery-errors B through E with the cited node statements open. There are no new-node form issues or unsearched leaves. The item is self-contained, retains all coefficient and domain qualifications, and uses single-escaped TeX after JSON decoding. I read each of the three mathematical ingredient statements in full, as well as def-sf-datum and the definitions def-sf-pf and def-exchange-projection.

Step 1 uses fix-lem-exchanges for the canonical comparison conventions in its pasting laws, lem-pur-derived-pullback-tensor-iso for natural monoidality compatible with composition, and def-sf-datum for the supplied domains of the displayed composites. The comparison c is from b_T followed by p versus p' followed by b_X. The comparison r is from g followed by b_Y versus b followed by g'. These are identifications of pullbacks, not assumed compact-support isomorphisms. Distributing w over the tensor and applying c gives exactly chi, including the q/b_Y square's pullback identification.

Step 2 uses clause 2 of fix-lem-exchanges twice and clause 1 for the canonical isomorphism of the outer square data. I checked that its statement explicitly says horizontal pasting and includes the pullback-composition maps at finite, completed and transported stages. The first path changes base by g then b_Y; the second by b then g'. Both end at Y', with upper corner T'. The resulting equality has source v Lg* F and target Rq'! P'; the c and r factors have the needed directions.

Step 3 uses the displayed base-change square AND the naturality assertion of prop-sf-pf-coherence, not its proof. The first input is P on T, the second is L on Y, and the base map is b_Y. T' is T times_Y Y', so the square is Cartesian. Naturality in c converts wP to P', giving A on the bottom left and chi on the right. P and L are on the finite-Tor domain supplied by the datum; no claim of unrestricted preservation is being inferred. The cited proposition covers the specified coefficient comparisons.

Step 4 uses the naturality clause of lem-pur-derived-pullback-tensor-iso. All remaining operations are explicit substitutions of the earlier two equations, functoriality of v and tensor, and associativity of composition, so this assembly step is marked elementary. The naturality square for mu is displayed rather than hidden in the word transport. The cited exchange and PF statements already assert their identities on completed and field domains, so no faithfulness of reduction or choices of arbitrary lifts are required. The final formula is exactly beta-prime composed with delta.

I checked the edge cases b=id and g=id: horizontal pasting becomes the identity-square law or the single exchange for f along b, while the final equation becomes PF naturality/base change. If K or L is zero both sides are zero. These checks preserve all directions of c, r, chi and delta. Every step is under 1000 characters, and none hides a new comparison lemma: the non-elementary comparisons are exactly the existing three cited statements. Generic off-unit tools are declared only in split_report.tool_uses; no accepted tool_uses field is written. The route remains clause (iii) of the relative-product unit, before the outer direct image and PF.

## Unfinished work

None in this stage-1 split. The mandatory server dry run passed. The delivery remains subject to the maintainer's independent mathematical review.
