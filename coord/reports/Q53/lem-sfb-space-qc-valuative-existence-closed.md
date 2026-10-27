# Q53: lem-sfb-space-qc-valuative-existence-closed

## Files written

All node files are under dag/nodes/sec-six-functors-basics/ in this sandbox.

- lem-sfb-space-qc-valuative-existence-closed.json: item, statement unchanged, now split into four steps following Stacks 03KA.
- lem-sfb-scheme-specialization-prescribed-field-probe.json: new statement-only unsplit node, Stacks 01J8(1)-(2); no Mathlib declaration of this prescribed-field assertion found.
- lem-sfb-affine-spectrum-specialization-stable-image-closed.json: new Mathlib leaf, PrimeSpectrum.isClosed_image_of_stableUnderSpecialization, Mathlib/RingTheory/Spectrum/Prime/Topology.lean:865-874, the closed-subset form of 00HY.
- lem-sfb-space-universally-closed-affine-tests.json: new statement-only unsplit node, Stacks 03IT(3) implies (1); Mathlib's analogous API concerns schemes.

citations.json contains a verbatim statement quotation for each dependency of each of the four steps. searches.jsonl and the saved search outputs record the executed msearch queries; search-plan.json relates the original searches to the individual new nodes. No Lean was written or compiled.

## Attachments

None. Searched lean/WeilConjectures by the item id and by AlgebraicSpace, algebraic space, valuativeCriterion, Valuative and UniversallyClosed. The project valuation results in Compactification/ValuativeCriterion.lean and Mathlib/AlgebraicGeometry/ValuativeCriterion.lean concern schemes. Scheme.exists_valuationSubring_of_specializes at lines 219-235 of the latter file fixes the algebraic closure of the general point's residue field; it does not prove the new prescribed-field probe. The existing node lem-trf-valuation-ring-specialization-lift already records that restricted assertion. None proves this item for algebraic spaces, including its field-extension existence hypothesis.

## WANTED

None. Read local spaces-morphisms.tex, algebra.tex and schemes.tex. The active blueprint read was literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3), as well as the chapter/unit records. This item is an auxiliary below the inherited Picard/alteration prerequisite chain, not the key theorem of its unit; no realization fields are changed.

## Audit and changes

The item is exactly the one-way implication Stacks 03KA, with the existence notion from 03IX, not the scheme-only criterion where the field need not be enlarged. Retained all hypotheses and the full conclusion. Its proof was empty. The four steps now perform the affine base change explicitly, choose an affine etale atlas, show specialization stability using a valuation probe and domination, and close the image by the Mathlib spectrum lemma. The new nodes do not restate the item's conclusion: the affine test lemma assumes closed maps on every affine test and says nothing about valuations, the probe only concerns a scheme specialization with fixed generic field, and the leaf concerns a ring map with a closed subset.

The atlas step uses Mathlib's closed-subset form directly, so it does not need an extra node constructing a closed subscheme from the closed inverse image. The base-change lifting argument is written with both components and the fibre-product universal property, rather than moving this elementary argument to another node. Corrected a draft source tag for this base-change argument to 03IY after checking tags/tags; the item itself is 03KA.

The ancestry command returns blueprint.from.node = None for this inherited creation chain. Retained that null root and the complete recorded via list, and added precise auxiliary places for each new node. No blueprint root was invented. Searches of the whole DAG by tags 03KA, 03IX, 03IT, 00HY, 01J8 and 00IA and by valuation/specialization/affine-image keywords, together with blueprint_refs.py searches for valuative, valuation, specialization, 03IT, 00HY and 01J8, found no existing node stating the three new assertions. The broader closed search was also inspected for relevant matches. Existing affine-atlas and point-topology nodes are reused.

## Not duplicates

lem-sfb-scheme-specialization-prescribed-field-probe vs lem-trf-valuation-ring-specialization-lift: the existing node permits only a fraction field that is an algebraic closure of kappa(y-prime); the new node must preserve the arbitrarily specified field K of the original map to the algebraic space. A representative of x-prime need not be defined over that fixed algebraic closure, so the restricted assertion cannot be substituted here.

lem-sfb-scheme-specialization-prescribed-field-probe vs lemma-nagata-valuation-ring-extension: the existing node extends an already given valuation ring to a larger field; it does not construct a valuation probe for a specialization of scheme points or specify its map to the scheme.

lem-sfb-scheme-specialization-prescribed-field-probe vs sk-lem-wrp-normal-geometric-cover: the existing statement is a representability/geometric-cover criterion for a separated etale map over a connected normal scheme, with a valuation condition on components. The new statement is a valuation probe in an arbitrary scheme and has no cover, normality or etaleness hypothesis.

lem-sfb-scheme-specialization-prescribed-field-probe vs lem-per-valuation-normalization-localizations: the existing node describes localizations of the integral closure of a given valuation ring in a finite algebraic extension, and a dominating ring containing that integral closure; the new node concerns arbitrary field-valued scheme points and specialization, with no finite extension or normalization.

lem-sfb-space-universally-closed-affine-tests vs lem-sfb-representable-stack-universally-closed-test: the latter tests universal closedness of a representable stack map by universal closedness of all scheme base changes. The new lemma tests ordinary closedness on affine scheme base changes. Neither quasi-compactness nor valuative existence occurs in either statement; the new assertion supplies exactly the weaker affine-test hypothesis used in 03KA.

## Review by Q53

I checked the item against spaces-morphisms.tex, lemma-quasi-compact-existence-universally-closed (03KA), and its hypothesis against definition-valuative-criterion (03IX). In particular the lift is allowed over A-prime with fraction field K-prime. The proof only uses domination to send the closed point of Spec A-prime to the closed point of Spec A; it does not assume that the ring extension is finite or etale. I read lemma-points-specialize (01J8) in schemes.tex in full, including its construction from a valuation ring dominating the image of the local ring. Its second clause permits exactly the field K already in the generic square; equality of the generic restriction is part of that prescribed extension. I read algebra.tex lemma-image-stable-specialization-closed (00HY) and checked the stronger closed-subset version directly against Mathlib lines 865-874. I read spaces-morphisms.tex lemma-universally-closed-local (03IT), including its proof via a disjoint union of affine etale charts; the new test node is its implication (3) to (1).

For step 1 I opened lem-trf-space-fibre-products-etale-covers: its statement supplies the sheaf fibre product as an algebraic space and the categorical universal property. Those are exactly the facts used. The compactness of P comes directly from the item's own affine-test hypothesis, so no general base-change compactness theorem is silently invoked. The lift into P is the pair of the hypothesis's lift to X and the fixed map to T; checking each projection proves the required equalities, including the generic equality. This is why this step is elementary.

For step 2 I opened lem-sfb-qc-space-affine-etale-atlas: it assumes only compactness of the point space and explicitly imposes no separatedness or quasi-separatedness. That matches P from step 1. I opened lem-a1-space-affine-etale-cover: it supplies continuity for every scheme-source map and surjectivity on points of the atlas. Thus D is closed and its image equals p(C). I opened def-weil-affine-spectrum: it explicitly identifies every morphism between affine spectra with a unique ring homomorphism. No finite-type condition on that homomorphism is used.

For step 3 I opened def-a1-algebraic-space-point-classes: it supplies field-valued representatives and equality of their classes after field extension. The new probe applies to the composite to the scheme T, whose generic image is y-prime, with the same field K; it is not applied to the algebraic space P. The conclusion of that new node is precisely the bottom valuation arrow needed by step 1. I checked that domination gives contraction of the maximal ideal, that (0) specializes to the maximal ideal in the domain A-prime, and that the scheme-source continuity statement of lem-a1-space-affine-etale-cover takes this specialization to P. A closed C contains its specializations. No lifting of a specialization through the atlas is assumed.

For step 4 the closed subset D and specialization-stable image are exactly the hypotheses of the new Mathlib leaf. Its conclusion gives closedness of p(C); the new 03IT node then applies for every affine T. I compared its actual conclusion with universal closedness in the item, including arbitrary algebraic-space base changes. Every node used in these steps has its full relevant statement copied verbatim to citations.json. The off-unit point-topology and fibre-product results are generic tools; the former is declared in split_report.tool_uses, and the latter is also an ordinary categorical construction already used by the statement, not a replacement of the unit's route.

I tested small cases: the empty source makes the closed-image argument vacuous; for y-prime = y the probe allows A = K, so no strict specialization is assumed. The zero ring yields empty affine spectra, allowed by the Mathlib leaf and by the empty atlas. Arbitrary closed subsets, non-Noetherian rings and non-quasi-separated algebraic spaces are permitted: no constructibility argument or finite-type Chevalley theorem appears. Field extensions leave the point class unchanged, while domination is essential for the special point. The three new files carry statements only, with empty proof/dependency lists for the proof. None asserts data chosen by a sorry or changes a target. All four proof steps are under 2000 characters (705, 580, 1161, 385), and I checked that none conceals another non-elementary assertion beyond its cited statements. The statement of the item needs no dispute or correction.

## Unfinished work

The two unsplit supporting lemmas intentionally remain statement-only stage-1 tasks. The present item's argument and searches are complete; server dry run and direct delivery follow.
