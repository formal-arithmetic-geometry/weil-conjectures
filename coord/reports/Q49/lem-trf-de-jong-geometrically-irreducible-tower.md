# Q49: lem-trf-de-jong-geometrically-irreducible-tower

## Files written

- dag/nodes/sec-trace-formula/lem-trf-de-jong-geometrically-irreducible-tower.json: item, split into eleven proof steps; statement retained exactly. Added fibre-product and generic-point definition dependencies.
- dag/nodes/sec-trace-formula/lem-trf-excellent-base-marked-semistable-curve.json: statement-only input, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-geometrically-integral-curve-factorization.json: statement-only input, unsplit; no Mathlib match.
- citations.json: literal statement quotations for all step/node pairs.

## Attachments

None. Searched the entire WeilConjectures source by the item tag and by de Jong, semistable/plurinodal, relative curve, and geometric generic-fibre terminology. No matching project declaration was found. Master sorry declarations were not treated as proofs.

## Wanted literature

WANTED: literature/de-jong-families-curves-alterations-1997.pdf, Theorem 2.4 and Remark 2.5 (printed pp. 602--603), Lemma 5.2 (pp. 612--613), Situation 5.8 and Theorem 5.9 (pp. 615--617), for this item and both new inputs. The complete publisher PDF was read online at https://www.numdam.org/item/10.5802/aif.1575.pdf; nothing was downloaded or written into literature. The item's proof_origin is agent, as required for a missing local document.

## Corrections and scope

The original statement is faithful to de Jong 5.9 after forgetting groups, projectivity, quasi-splitting and boundary data. No statement dispute was found. The original node had no proof and no Lean audit. The new proof follows de Jong's induction on generic dimension but, since the item asserts no group action, uses finite generic-component splitting in place of the Galois bookkeeping of Lemma 5.5. This stays within the same relative-curve/semistable-alteration route. Quasi-splitting Lemma 5.7 is unnecessary: every required nodal condition is already geometric.

The existing marked semistable nodes assume their base is projective over an affine Noetherian scheme; the item has no such assumption. The existing curve-factorization/preparation nodes assume the original base is a field or trait. Neither can be applied to the arbitrary excellent base here. The two new inputs remove precisely these unsupported applications. The marked curve theorem is a genuine dimension-one input (arbitrary generic curve, marked boundary and sections), not a renamed theorem asserting towers in all dimensions. The factorization gives no semistable alteration or tower at all.

## Mathlib and blueprint searches

All fifteen new searches are preserved verbatim in searches.jsonl and their full signatures in work/search-0.txt through work/search-14.txt. Every node was searched by LeanFinder twice with different phrasings, Loogle, grep, and LeanSearch. All services answered; none was marked unavailable. The item searches found ordinary dominance, normalization, properness and smooth base change. The curve searches found ordinary Proj facts, Weierstrass good reduction over a DVR, smoothness, flatness and Lagrange nodal polynomials. The factorization searches found rational maps, normalization, scheme-theoretic images and properness of a composite. I read all these returned signatures: none constructs the objects required by either new statement or specializes to it in one line.

Whole-DAG searches used de Jong, Theorem 2.4, Lemma 5.2, semistable, plurinodal, curve factorization, geometric generic fibres, and the exact tag/label 02JX / lemma-alteration-dimension. The tag search found only the existing dimension node and its parent hypercover node; both comparisons are recorded below. Whole-blueprint searches used semi-stable, semistable, geometrically integral, geometrically irreducible, Stein factorization, curve factorization, and geometrically reduced and irreducible generic. The matching definition nodes were reused; no blueprint theorem states either new input. The ancestry is the existing chain back to lem-trf-local-term-locality; its current proof's normal-cone-specialization sentence is named in all blueprint.from.place fields. No unit or chapter record was changed.

## Not duplicates

lem-trf-excellent-base-marked-semistable-curve vs lem-trf-dejong-relative-marked-semistable: the existing theorem assumes a base projective over an affine scheme and an already smooth generic curve; the new theorem allows an arbitrary excellent integral base and any integral generic curve, with de Jong 2.4's preliminary alterations included.
lem-trf-excellent-base-marked-semistable-curve vs lem-trf-relative-marked-nodal-reduction: the same base/projectivity and generic-smoothness restrictions prevent the existing theorem from giving the new statement.
lem-trf-excellent-base-marked-semistable-curve vs lem-trf-plurinodal-alteration: the latter is for a strictly henselian equal-characteristic trait (and its separate field clause), whereas the new theorem is a marked relative curve theorem over arbitrary excellent integral schemes.
lem-trf-excellent-base-marked-semistable-curve vs lem-trf-de-jong-geometrically-irreducible-tower: the new theorem concerns only relative dimension one, does not assume geometric irreducibility of the input generic curve, and supplies marked sections/boundary control; it is used as the base and single-curve input to a real induction, not as a replacement for the tower conclusion.
lem-trf-geometrically-integral-curve-factorization vs lem-trf-relative-curve-factorization: the old statement assumes a field or trait base and only gives transcendence degree one, whereas the new statement permits arbitrary excellent bases and gives geometric integrality of both generic fibres after a birational modification.
lem-trf-geometrically-integral-curve-factorization vs lem-trf-alteration-relative-curve-preparation: the latter assumes a field or trait and also handles an inseparable boundary; it does not apply to the new input's arbitrary excellent base.
lem-trf-geometrically-integral-curve-factorization vs lem-trf-closed-dominant-dimension: the shared Stacks Tag 02JX is used only for finiteness of total dimensions; that node is a dimension formula and constructs no relative-curve factorization.
lem-trf-geometrically-integral-curve-factorization vs lem-trf-plurinodal-proper-hypercover: the shared Stacks Tag 02JX occurs in that node's dimension bookkeeping; the hypercover theorem does not give a birational relative-curve factorization with two geometrically integral generic fibres.
lem-trf-geometrically-integral-curve-factorization vs lem-trf-de-jong-geometrically-irreducible-tower: factorization gives proper maps with geometrically integral generic fibres, without semistability, flatness or any tower of nodal curves.

## Review by Q49

I read the chapter record and sk-i-curve-zero unit, the current main-20261015 blueprint proof of lem-trf-local-term-locality, the parent plurinodal-hypercover split, and all cited DAG statements. I read de Jong 5.9's statement and proof, 5.8's curve-tower definition, 5.2's separating-transcendence-basis/Stein-factorization proof, and 2.4 with Remark 2.5. I checked the local Stacks text for 04KT (finite inseparable geometric reduction), 054Z (reduction of generic fibre), 02JX (closed-dominant dimension), 02NW (generic finiteness), and 07QU (excellence under finite type/localization). I checked delivery-errors B--E against the actual statements, not just the dependency arrays.

Step 1 uses the new marked curve theorem with empty boundary. Its generic-dimension-one hypothesis is exactly available, and it gives the reduced, connected, pure one-dimensional fibres and completed nodal rings the item needs. Strong induction is explicitly uniform in all excellent bases and the induction is only called at d-1.

Step 2 uses finite inseparable geometric reduction on the single component of the integral finite-type generic fibre. The normalization statement supplies both its construction and its function field. The excellence-to-Nagata statement and the two Japanese definitions give finiteness on every affine domain chart; finite-proper then gives properness and closedness. No shrinking of the original base is used, unlike the generic-preparation nodes whose conclusions only hold on an open.

Step 3 uses the reduced-closed-subscheme statement for the actual closure, 054Z for its generic fibre, and the proper permanence statement for the closed subscheme of a proper base change. I explicitly checked geometric irreducibility after further field extension: the reduction ideal remains nilpotent, so the underlying space is that of the corresponding base change of the original geometrically irreducible fibre. Geometric reducedness comes from Step 2. Finite base change and quotient finiteness are written from finite module generators, rather than inferred from a definition without an argument. The dimension formula applies to the finite dominant generic-fibre map.

Step 4 uses precisely the two geometrically integral generic fibres supplied by the new factorization input. The original base is arbitrary excellent, and d is at least two. The proper modification has an isomorphism over a dense open, so it really is an alteration.

Step 5 uses the new relative curve theorem without assuming a projective-affine base, and the proper-composition statement. The dimension/transcendence-degree node says exactly that a finite function-field extension does not change the generic dimension of B over S_0. I do not assume this altered generic fibre remains geometrically irreducible.

Step 6 repairs that issue using the existing finite separable component-splitting statement. I checked its quantifier over all field extensions and the fact it asserts irreducibility, not reducedness. Only irreducibility is needed for the induction. The finite normalization is constructed with the same exact normalization/Nagata/Japanese citations as Step 2. A prime of k(B) tensor L supplies a component dominating B; the finite-dimensional algebra has no strict prime inclusions after localization. The reduced closure statement supplies B_2, 054Z gives its reduced generic fibre, proper permanence gives properness, and 02JX gives relative dimension d-1. These are the complete hypotheses of the induction application.

Step 7 uses the induction conclusion and proper-composition node. The dense-open proof of composition of alterations is spelled out: remove the finite closed image of the bad closed set upstairs. Integrality and finite dominance ensure that bad image misses the target's generic point. This also proves the corresponding compositions in Step 10 without treating generic finiteness as an unstated theorem.

Step 8 uses the fibre-product universal property and the three permanence statements for properness, flatness and finite presentation. I read the finite-presentation permanence node's clause (3), rather than taking it from its title. The geometric fibres are literally the same geometric fibres at composite geometric points; hence all nodal and connectedness clauses persist. This is an elementary specialization, not an additional nodal-base-change lemma.

Step 9 checks integrality of the whole final fibre product, which cannot be replaced by selecting a component because that could lose flatness. The cited affine flatness criterion really gives flat coordinate rings, and the flat-ring-map definition preserves the injection into the fraction field. Thus every nonempty affine chart embeds in a domain from the integral generic fibre and meets that fibre. Reducedness and irreducibility follow as written. This is a short affine argument from the cited statements and definitions, not an unproved general assertion hidden under 'standard'.

Step 10 uses proper and surjective base change and gives the finite algebra generators after base change. The relevant inverse image of a dense base open is nonempty and dense because the integral C dominates B. The commuting squares give precisely the claimed structural equality, with no assertion of surjectivity onto vertical components of W times_S S_1.

Step 11 uses the exact finite-type excellence statement and the finite-type-over-Noetherian statement, and the dimension formula for integral proper dominant maps. I checked the relative function-field degrees zero or one in every use. The bookkeeping does not introduce a circular induction: it derives finite dimensions for intermediate B and B_2 before the lower-dimensional induction is needed, and derives P's dimension only after the induction produces Q. It also supplies the base case's finite total dimensions. Every cited statement is quoted literally in citations.json.

For small cases I checked d=1, d=2, S a field, imperfect fields with geometrically irreducible but nonreduced geometric fibre, empty boundary, a smooth family with no singular points, and bases whose altered fibre product has vertical components. The inseparable reduction addresses the imperfect-field case; the component choice does not discard required points of W because the map to integral W is finite dominant. The zero-dimensional case is deliberately outside the item and is handled separately by its parent. No invertibility of alteration degrees, generic smoothness of the input, normality of the base, affineness, or projectivity of the base was added. All eleven steps are below 2000 characters. The two new nodes contain statements only, with no proof sketches or proof dependencies.

## Unfinished work

None for the one-level split. The two new statement-only inputs remain queued for their own later splits. No Lean was written or compiled and no live repository/launcher file was changed.

## Validation

The first full deliver.py --no-push completed with OK at 91f8456272. A final dry run follows the completed same-tag duplicate comparison; delivery is made only after that process exits successfully.
