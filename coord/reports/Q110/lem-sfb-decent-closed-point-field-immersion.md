# Worker report: lem-sfb-decent-closed-point-field-immersion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-decent-closed-point-field-immersion.json: item, split following Stacks 0AHB into five steps; no mathematical statement change.
- dag/nodes/sec-six-functors-basics/lem-sfb-decent-etale-fibres-no-specializations.json: statement, unsplit, no Mathlib match. Stacks 03K5 with decency written explicitly.
- citations.json: verbatim statement quotations for every step/node pair.
- report.md: this report. searches.jsonl from the interrupted attempt was retained and read; subsequent actual searches extend it.

## Attachments

None. The required id and concept searches under lean/WeilConjectures found no project declaration stating this algebraic-space assertion. Scheme residue-point declarations do not attach it. No Lean files were written or compiled.

## Wanted literature

None: the required Stacks source files and tag table are present.

## Corrections and unfinished work

The item was unsplit. Its statement is faithful to 0AHB: 03JV (6) is the stated hypothesis, and (4) supplies monomorphic representatives. There is no STATEMENT-DISPUTED claim. The exact statement text is preserved; all statement and proof strings use single TeX backslashes after JSON decoding. No hypothesis of quasi-separatedness, Noetherianity, finite type, or rationality over S was added. The imported unit record is older than literature/blueprint/latest; I read both, retained the existing ancestry and route, and changed neither unit nor chapter.

The source's residue-field sentence is expanded: first closedness gives the canonical residue-point closed immersion; pullback along it and 03DP identify the nonempty monomorphic fibre with that residue spectrum. This also proves distinctness of the component images, without incorrectly assuming monomorphisms are automatically immersions. Only the 03K5 input is left as a new statement-only node. Existing representative and descent nodes were reused. No part of the conclusion is merely moved into a new node.

## Review by Q110

I read decent-spaces.tex at lemma-decent-space-closed-point (0AHB), lemma-UR-finite-above-x (03JV), definition-very-reasonable (03I8), and lemma-decent-no-specializations-map-to-same-point (03K5). For the new node, 03K5 states exactly equality of comparable chart points with equal image, with decency; 03JV (4) is its explicit decency hypothesis. I also read morphisms.tex lemma-etale-over-field (02GL), schemes.tex lemma-mono-towards-spec-field (03DP) and its proof, and spaces-morphisms.tex lemma-closed-immersion-local (03M4). The current blueprint direct-images proof retains the compactification/proper-image route from which this supporting geometric input descends.

In step 1 the representative node has exactly the item's all-field-maps-quasi-compact hypothesis and gives the needed quasi-compact monomorphism at every point. The algebraic-space definition supplies a representable surjective etale atlas; the affine-open-basis statement supplies its affine refinement. This is not the quasi-separated-only field-representative theorem.

In step 2 the topology definition makes the inverse image of the closed singleton closed. The new 03K5 node has its hypothesis from step 1, and rules out every proper specialization inside that fibre, proving that its individual points are closed. The fibre-product node explicitly gives scheme representability and etaleness of the chart pullback. The item's quasi-compactness condition applies because the chart is affine. The etale-fibre node states the disjoint-union-of-field-spectra assertion with discrete singleton opens; quasi-compactness makes their covering finite. Applied over Spec K, its unique residue-field fibre is W itself, by the identity base-change universal property.

In step 3 I checked the statement of every cited scheme node. The residue-point-immersion node applies because the chart images were proved closed in step 2. The morphism-from-spec-field node gives the precise canonical factorization. The field-point-through-immersion node gives uniqueness through that closed residue-point map, so pulling back each such factorization returns the original field component (a pullback of a map through a monomorphism along that monomorphism). Components with other images contribute the empty scheme. Monomorphy of q and of its pullbacks is checked directly on pairs of maps using the fibre-product universal property; it is not an uncited geometric theorem. The existing 03DP node classifies every monomorphism into a single field spectrum as empty or that spectrum. Thus it identifies the nonempty fibre, proves distinctness of images and equality of their residue fields, as 0AHB needs.

Step 4 is elementary from the closed-immersion definition and the already proved component immersions. Finite closed singleton images have discrete subspace topology. On the complement of all but one of them, the sheaf map is the corresponding component surjection; on the complement of all of them it has zero target. These open neighbourhoods cover the target. This writes the local-surjectivity argument explicitly rather than hiding a Chinese-remainder or finite-coproduct theorem. The argument also covers zero components.

Step 5 uses the existing atlas-locality statement, which expressly does not assume the map representable in advance and concludes representability and closed immersion on every scheme test. The affine charts from step 1 are jointly surjective, precisely its hypothesis. No finite cover or separated target is assumed. Generic tools outside the imported unit are declared in split_report.tool_uses; no unit route was replaced.

I checked B--E of delivery-errors.md: the sole new node is self-contained and statement-only, all notions have actual definition references or inline meanings, its exact tag is in tags/tags, and its searches are real logged queries. I searched the whole DAG, the blueprint via blueprint_refs.py and the project source before creating it. The quasi-separated-only specialization node cannot be used under mere decency. Every uses entry has a literal statement quote in citations.json; no proof of a cited node is being used as its statement. Small cases checked are the empty chart fibre, an empty X (no x, hence vacuous), X=Spec K, several distinct closed chart points over the same space point, and a nonclosed chart image (excluded by the actual 03K5 argument). Arbitrary base S and infinite atlases remain allowed. All five steps have fewer than 2000 characters. The server-only review_split check passed before this report was written; final delivery preflight is recorded below when run.

## Not duplicates

lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-space-topological-dimension-local-rings: existing conclusion is a dimension formula under quasi-separatedness; new conclusion is equality of comparable chart points under decency.
lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-qs-space-field-monomorphism: existing conclusion is existence of field representatives under quasi-separatedness, not specialization equality.
lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-quasiseparated-space-sober: existing conclusion is sobriety under quasi-separatedness, not the chart-fibre assertion under decency.
lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-decent-quasicompact-monomorphic-points: existing conclusion supplies representatives; it does not assert absence of chart specializations.
lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-field-monomorphism-finite-chart-decency-criterion: existing conclusion is quasi-compactness of field maps, not chart-point specialization equality.
lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-decent-algebraic-field-image-closed: existing conclusion concerns a field point over a closed base point with algebraic field extension; new conclusion concerns arbitrary comparable chart points without a base-point hypothesis.
lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-relative-qs-affine-chart-point-fibres: existing conclusion is finiteness of fibres under a quasi-compact diagonal and an affine-base factoring condition; neither hypothesis is available here.
lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-smooth-integral-fibre-vertical-divisors: existing conclusion compares divisor groups for smooth maps to regular locally Noetherian bases; new statement has none of that setting.
lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-finite-chart-fibres-field-quasicompact: existing conclusion is quasi-compactness of field maps from finite point/relation fibres; new statement does not assert that implication.
lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-quasiseparated-space-etale-specializations: existing equality clause requires a quasi-compact diagonal. New statement assumes only decency, so the existing node cannot specialize to it under the hypotheses in force.
lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-locally-separated-rational-point-closed-immersion: existing assertion concerns rational sections of locally separated spaces over fields; new assertion concerns arbitrary etale charts of decent spaces.
lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-decent-closed-point-field-immersion: item concludes existence of a closed field subspace at a closed point; new statement concerns comparable arbitrary chart points and does not conclude any closed immersion.
lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-decent-space-finite-field-map: existing conclusion is finiteness under a finite extension of a closed base-point field; new assertion has neither such input nor conclusion.
lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-locally-separated-space-decent: existing assertion derives decency from a locally separated diagonal; new assertion takes decency as input.
lem-sfb-decent-etale-fibres-no-specializations vs lem-sfb-qs-space-rational-point-topology: existing assertion concerns rational points over a field and assumes quasi-separatedness; new statement has arbitrary scheme base and only decency.

## Validation

Server review_split: PASS. The delivery dry run exited 0 and printed OK (not pushed) at 00cd2a6a341; server preflight, check_dag and review_split passed. Final report is revalidated before the push.
