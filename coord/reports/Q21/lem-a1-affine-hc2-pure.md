## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-a1-affine-hc2-pure.json: statement item split; no Mathlib match.
- citations.json: verbatim statement quotations for every citation in every proof step.
- searches.jsonl: actual search-command log; retained as generated.

## New nodes

None. Zero Mathlib leaves created. The eigenvector scaling and absolute-value calculation are elementary steps, not new lemmas.

## Attachments

No finished declaration states the item in the available checkout. The recorded old module WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper is absent. Searching the whole WeilConjectures tree by item tag and purity/cohomology names found instead the sorried weight-zero specialization AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_two_of_isAffine in DeligneLaumon/Reduction/RelativeAffineLine.lean:128, and the sorried middle-extension theorem in DeligneLaumon/AffineLine/Endpoints.lean:120. Neither is attachment evidence.

AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine belongs to existing node lem-sf-adic-affine-direct-image-finiteness. I read the declaration in SixFunctors/ProEtale/Adic/LowerStar.lean:411 and its existing node: the affine finite-type adic finiteness assertion matches. This accounts for the old audit's open entry with nodes: []; a duplicate is unnecessary. It is a sorried dependency, not a finished proof and not an additional hypothesis or ingredient of the present natural-language argument. The other old audit open entry already points to the endpoint nodes. Its old CurveEndpoints module is also absent; the current endpoint comparison is sorried in AffineLine/Endpoints.lean:109. The split below uses the independent blueprint top-cohomology interface already in the DAG.

## WANTED

None. The current blueprint statement and proof and all the ingredient statements were available locally.

## What was wrong or changed

The imported proof already gave the correct route but did not document the finite E versus Qbar_l passage, did not name the tensor Frobenius definition, and compressed eigenvalue transport and the zero case. I preserved the statement verbatim, expanded these arguments, supplied sources and definition dependencies, and marked the item split. I followed main-20261015, including the updated global-section formulation of geometric coinvariants, rather than treating the older snapshot as authoritative. There is no statement dispute and no change to the unit or chapter route. No SGA source is used.

## Unfinished work

None at the assigned one-level split. Existing cited nodes remain their owners' tasks; they were not resplit.

## Review by Q21

I read the chapter and unit records and the current main-20261015 item statement and all three paragraphs of its proof. The item supplies the degree-two endpoint input to the affine-line upper-bound unit; its proof has no need for the Fourier argument, ramification at infinity, or semisimplicity. I also read the current blueprint statements for lem-a1-affine-hc2, lem-a1-geometric-coinvariants-pure, and lem-wf-tate-twist-frobenius, the coinvariant and Tate-scalar proof files, and the full statements of every node cited by this delivery. There are no new nodes needing separate source review.

Step 1 uses exactly the Frobenius-equivariant H_c^2 isomorphism stated by lem-a1-affine-hc2. Its curve is smooth, affine and geometrically connected and its sheaf is lisse, exactly as required. I do not take a duality construction from that node's proof. Step 2 uses exactly the purity conclusion of lem-a1-geometric-coinvariants-pure with the same curve, weight and sheaf. The original node's hypotheses are satisfied; its blueprint_update also applies since the curve is locally finite type and geometrically connected, and explicitly identifies the dual-section definition with the geometric coinvariant quotient and induced Frobenius.

For step 3 I checked the coefficient issue: lem-wf-tate-twist-frobenius states the E-valued stalk scalar, so it is applied at the rational point of Spec k_0, not a degree-d point of the curve. The existing lem-pur-twist-frobenius-scalar explicitly states rank one, the global point scalar q^{-m}, and compatibility through Qbar_l scalar extension. At m=-1 this is q, not q^{-1}. The tensor formula in clause 5 of def-weil-frobenius-coefficient-twists is the precise definition used to obtain q F_W, and clause 4 supplies the finite-stage meaning. Thus no definition node is used as a surrogate for the scalar theorem. I corrected the missing coefficient justification by citing these existing interfaces.

Step 4 is elementary: the same nonzero vector is an eigenvector of F_W for beta/q; q is positive and nonzero; iota fixes q; absolute values multiply; real exponents add. The purity definition is quoted, and equivariance of the isomorphism explicitly carries nonzero eigenvectors to nonzero eigenvectors. This avoids using a spectral theorem or a hidden semisimplicity assertion. The tests were the zero sheaf/zero coinvariants (vacuous purity), a geometrically constant rank-one sheaf (eigenvalue lambda becomes q lambda), and a nonsemisimple Frobenius block (the calculation uses individual eigenvectors and remains valid). Arbitrary real w and the absence of rational points on the curve cause no additional hypothesis: the scalar computation is on Spec k_0.

I checked delivery-errors B through E: statements are not weakened; no new elementary, duplicate or clause-restating nodes are introduced; citations take only the cited statements; all non-elementary inputs are named; proof_deps is exactly the union of uses; TeX is encoded once. Every proof step is below 2000 characters. The blueprint and full-DAG searches located the existing coinvariant/top-cohomology/Tate interfaces; other top-degree bounds and the weight-zero disconnected-curve lemma are not equivalent statements, so same_as is empty. Searches used two semantic phrasings, Loogle and source grep through msearch.py and their actual results were read. Hits about ordinary cohomology, group invariants, inseparable Frobenius, function support, and Lie weights do not supply the item.

The off-unit top-cohomology and Tate-scalar results are declared as generic tool uses in split_report: the blueprint already takes the curve endpoint and Tate-line formula as tools. The Qbar_l point-scalar lemma makes that formula precise; it does not replace the unit route. The report and citations are my own review of the split, for the maintainer's independent review.
