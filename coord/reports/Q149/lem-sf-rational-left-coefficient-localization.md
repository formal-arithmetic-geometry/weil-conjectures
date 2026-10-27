# Q149 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors/lem-sf-rational-left-coefficient-localization.json: statement unchanged, four proof steps; no complete Mathlib match.
- citations.json: six verbatim statement excerpts for the six step/node citations.
- searches.jsonl: five actual new searches, retaining the earlier Q148 searches in the item.

New nodes: 0. New Mathlib leaves: 0. The domain theorem and raw-localization definitions already exist, and extracting a further localization-of-an-equation lemma would create an elementary node.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for rational coefficient localization, scalar localization and coefficient cocycle/coherence. The results concern rational closed-support localization, module-object rationalization and other coefficient cocycles, not all clauses of this item. Read LocalizationRational.lean and the context of UpperShriekCanonicalMapsCoherence.lean; neither states this normalized completed-coefficient assertion.

## WANTED

None.

## Findings and changes

The imported item had an empty proof. Its statement already includes the rational morphism normalization needed to identify F(alpha) and F(u); I retained it verbatim. Object equalities and localized q components alone would not justify those terms. The proof uses the singleton coefficient-1 case of the full normalization; it does not assume localization reflects equality.

The blueprint.from.node was null despite the creating item's recorded ancestor being sk-thm-sf-tensor-hom. The blueprint ancestor command exposed the null; reading lem-sf-constructible-exceptional-coefficient-coherence showed that its ancestor is sk-thm-sf-tensor-hom. Filled this ancestor and its final coefficient-compatibility place, retaining the creating-item via list. Searches of the whole blueprint for rational localization, scalar localization and coefficient cocycle found definitions and broader coefficient assertions, not another statement of these hypotheses and conclusions. No new nodes or unit records were needed.

The five new Mathlib searches used msearch.py and their returned results were read. Localization.linear/functor_linear and liftNatTrans_app concern generic localization structure, Trifunctor.lean localizes trifunctors and associators, and CommRingCat.moduleCatExtendScalarsPseudofunctor concerns ordinary module categories. They do not also supply the integral constructible representative with uniform Tor bounds or the given completed scalar identifications. The second semantic phrasing returned cotangent and group cohomology results, which do not match. The Loogle map_comp result explains an elementary equality used directly; it is not the full item. No unsuccessful service was represented as an absence result.

## Unfinished work

None in this one-level split. The independent maintainer review remains the project review.

## Review by Q149

I read the stage-1 brief, stages/1-dag.md, the fixed chapter record, sk-thm-sf-compatibility's statement and coefficient clause, SETUP's three blueprint levels, GOAL.md and both copies of delivery-errors B through E. For the item I read the current exceptional-inverse-image source at literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md, especially its integral/rational/common-stage paragraph, and the sk-thm-sf-tensor-hom source's final compatibility assertion. Neither spells out the present arrow calculation, so proof_origin is agent. I also read the full statement and proof of the creating coefficient-coherence node. It invokes precisely this normalized rational argument, not a new purity or trace route. No SGA source is used.

For step 1 I opened def-weil-rationalization-karoubi and lem-coef-integral-residue-tor. The first really keeps all integral objects and takes Hom tensor E without Karoubi completion. The second really says every derived-complete integral constructible object has one Tor interval at all positive reductions; it is not merely the definition of finite Tor amplitude. I read its source literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/lem-coef-integral-residue-tor.md, whose residue test gives exactly that consequence. The scheme X has ell invertible since its base field has characteristic p different from ell. No absolute separatedness is required. The uniform interval may depend on the representative; no uniformity across all objects or coefficient fields is claimed. This is the only non-elementary proof step and its cited theorem is already in the DAG.

For step 2 I checked the last paragraph of def-weil-rationalization-karoubi: it states the scalar-extension action on objects AND the pure-tensor arrow formula. Thus T sends R(h) to R(T_int(h)), with the coefficient embedded into the larger field. The F-image equalities instead come directly from this item's explicit morphism-normalization hypothesis with coefficient 1. The associators and unitors are localized integral arrows by a separate explicit hypothesis. Nothing is inferred about ordinary versus completed scalar tensors beyond those specified identifications. I opened def-weil-integral-scalar-extension and def-sf-categories to verify these are the completed small pro-etale categories, not constant-coefficient etale categories. This step is substitution of given equalities, so elementary.

For step 3 I opened def-weil-linear-scalar-localization: the displayed composition formula makes the image of a three-arrow integral composite exactly the three localized arrows. The rationalization definition supplies the scalar-functor term. The middle comparison is evaluated at T_int(Ktilde), which is precisely the integral representative used in the raw rational scalar functor's object definition. Each source and target therefore agrees under the stipulated identifications. Applying R_M to the integral equation and substituting gives the displayed rational composition equation directly. This uses no faithfulness, descent theorem or uncited non-elementary lemma.

For step 4 I used the same composition clause of the scalar-localization definition and wrote the localized integral unit equation explicitly. Its functor-image term is the one already computed in step 2; its remaining two terms are stipulated localizations. Step 1 covers every raw object, and the allowed field-embedding convention reduces to the same actual image inclusions. Thus the identity argument is elementary as well.

Small cases checked: the zero object; the empty scheme; an identity extension E=E=E; a nontrivial ramified inclusion (no flatness or exchange of inverse limits is used); and integral arrows killed by rationalization (applying R to an equality is still valid). These calculations require neither a faithful localization nor choices of rational idempotent summands. I compared every quoted dependency with its statement, generated verbatim excerpts, checked all four steps are below 2000 characters, and verified that proof_deps is exactly their uses union. There is no newly created statement to test or distinguish from a duplicate. The unchanged statement has no dispute. I corrected the missing blueprint ancestor and supplied the explicit F(alpha), F(u), composition and unit calculations that an instruction merely to localize would hide.
