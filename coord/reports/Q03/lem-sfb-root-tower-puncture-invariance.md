# Stage-1 worker report: lem-sfb-root-tower-puncture-invariance

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-root-tower-puncture-invariance.json: existing statement split into eight proof steps; statement unchanged, no new nodes, no Mathlib leaves.
- citations.json: a verbatim statement quotation for every node cited by every numbered proof step.
- searches.jsonl: the actual Mathlib search-command records. The pre-existing item searches remain in the item; the five new searches are appended with their actual results.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for puncture/root-tower/lisse/Kummer terminology. The hits concern unit Kummer covers and boundary stalk calculations, not the displayed derived unit on a full ramified parameter tower with all-continuous coefficients. No compiled or sorry declaration was treated as a finished proof.

## WANTED

WANTED: an exact all-continuous, norm-topological E/Omega proof of lem-sfb-root-coordinate-supported-vanishing, including incomplete Omega and arbitrary affine pro-etale charts. This is the already existing unsplit input, not a theorem claimed to be proved in this delivery. The finite-coefficient semistable Kummer-tower result and the finite tame-fibre classification do not supply that coefficient comparison. No new literature was downloaded or new node introduced for this obligation.

## Corrections and scope

The item had no proof; its source place describes an agent-extracted obligation rather than a theorem explicitly proved in the cited blueprint paragraph. The current main-20261015 direct-image proof paragraph (3) states preservation for open direct images via other nodes and supplies no all-continuous root calculation. I keep the statement unchanged and mark the proof as agent-written. I do not present the blueprint as an exact reference for the supported-vanishing input.

The useful existing result is lem-sfb-root-coordinate-supported-vanishing, found by the whole-DAG keyword search. Its conclusion concerns a single closed coordinate, including after other coordinates are inverted. Localization and a finite induction supply the arbitrary-subset theorem. This is not a newly created node restating a clause of the item. The root-tower lisse-morphism-extension node only gives underived Hom restriction for E; it does not prove the higher direct image or Omega assertion and is not cited. The boundary-acyclicity and inner-support statements have other conclusions, and the latter depends on this item, so neither is used circularly.

Whole-blueprint searches via tools/blueprint_refs.py search for 'puncture' and 'root tower' found no statement-equivalent imported node. The ancestor command explicitly reports blueprint.from.node = None for this inherited created-node chain; I preserve that inherited value and give the exact paragraph and obligation in from.place and split_report.blueprint.

## Review by Q03

I read coord/delivery-errors.md B--E, the item, its chapter and unit records, the current direct-image proof paragraph (3), and the statements of every dependency actually cited. For the localization step I also read the main-20261015 sk-lem-formal-closed-support-adjunction.md: clause 4 is precisely the triangle with the actual unit, for any condensed ring and a quasi-compact complementary open. For composition I read Stacks sites-cohomology.tex, Tag 0D6E, label lemma-derived-pushforward-composition, and derived.tex, Tag 09T5, label lemma-derived-adjoint-functors; the cited normalization node explicitly identifies units as well as functors. For coefficient realization I read Hemo--Richarz--Scholbach Example 3.1 and its discussion of colimit topology, and the cited generic transport/alpha statements. Those sources do not justify replacing norm-topological Omega by the finite-subextension-valued condensed coefficient. No SGA source is used.

Step 1 uses lem-sfb-alpha-iso for arbitrary condensed rings, not sk-prop-sfb-cartesian-coefficients, whose admissible Omega convention is narrower. The internal-module transport statement identifies the specified adjunctions, units and counits and gives exact equivalences to actual ring-sheaf modules. Together with the total-derived adjunction statement it lets us use exact inverse images in the following calculations. No flatness of a coefficient extension is assumed.

Step 2 uses the exact definition of profinite test objects as an affine pro-etale object obtained from Spec LC(P,Z) by base change. The root-algebra tensor identification is written by its generators-and-relations universal property. It applies to every finite root stage and compatible family of roots, so identifies the colimit tower, its root transitions, and the puncture. Lisse pullback follows directly by pulling back the finite free trivializing cover in the lisse definition; it makes no uniform-monodromy or finite-coefficient descent assertion. This absorbs P into the original affine pro-etale hypothesis, rather than assuming an unstated parameterized version of the vanishing input.

Step 3 uses exactly the existing supported-vanishing statement for the original N restricted to X_J and the pair (J,a). I checked the coefficient F=Omega, original chart hypotheses, the allowance of all J and a not in J, and its ordinary derived category. The closed support is V(t_a), including its scheme structure; it need not be a reduced coordinate face. The complementary principal open is quasi-compact, including on every affine open, so the localization triangle is applicable. Its first term vanishes and its middle arrow is exactly the requested one-coordinate unit. The zero-fibre criterion is the elementary consequence of the long exact Hom sequence of a distinguished triangle. No general pro-etale base-change theorem is inserted here.

Step 4 states a genuine induction, with J_0 empty and the actual unit as induction claim. The normalized composition node says the composite unit is the successive-unit composite; the ring-sheaf Grothendieck node and the exact internal/sectionwise equivalence verify its category hypothesis. Exactness of the pullbacks comes from step 1. The input vanishing is used once for each added coordinate, and the functor R(i_m)_* sends that isomorphism to an isomorphism. Enumerations give the same map because each is identified with the specified adjunction unit. I replaced an earlier general module-object Grothendieck citation by the concrete ring-sheaf version to make its hypotheses directly visible.

Step 5 is the naturality equation of the specified unit and multiplication by its inverses, using the derived adjunction node. Step 6 writes the mate that defines the usual exchange and transposes its composite with the pulled-back unit. The triangle identity gives the identity transpose on both sides; hence the two maps agree by the adjunction bijection. This is a short formal calculation, not an assertion of an uncited geometric base-change isomorphism: invertibility follows afterwards from the two clean units. It works for every parameter map, including nonsurjective ones, and for a pro-etale chart change because step 2 and base change of the root presentation put the new object under the same proven theorem.

Step 7 performs this calculation on the actual Q-parametrized action morphism and the supplied module-action isomorphism. The latter identifies its pulled-back module with the projection pullback already known to be clean. Preserving the indicated open gives the required open square. The equality is in the category on T[Q] (and T[P times Q]), not just its Q-points. The product identification of test objects follows from their finite-quotient limit definition. Step 8 checks empty A/r, empty P/chart, and rank zero. No argument needs completeness of Omega, a nonempty face, Noetherianity of the infinite tower, or a global cohomological-dimension bound.

There are no new statements to test for B1--B8, no same-tag new/existing pairs, and no missing new-node searches. Existing citations are supported by verbatim quotes in citations.json. All proof steps are shorter than 2000 characters. The dependency chain below the supported-vanishing input remains open on purpose: stage 1 splits by one level and does not claim a Lean proof or a proof of that separate item. I checked that none of the cited statements depends on this item. The generic localization, coefficient transport, module-category and adjunction tools do not replace the unit's tame-boundary route; their uses are declared in split_report as appropriate.

## Not duplicates

No new nodes. In particular I reuse lem-sfb-root-coordinate-supported-vanishing rather than creating a one-coordinate or reworded purity claim.

## Unfinished work

No required work on the split is left. The existing supported-vanishing input still requires its own stage-1 split and exact analytic reference. This report does not certify that input as proved.

## Validation

The preliminary server review_split check passed with zero new nodes. Full deliver.py dry-run and push results are recorded below after completion.
