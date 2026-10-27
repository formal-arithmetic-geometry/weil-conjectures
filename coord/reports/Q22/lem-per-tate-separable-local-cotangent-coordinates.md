## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-tate-separable-local-cotangent-coordinates.json: split statement, unchanged; no Mathlib match for the analytic assertion.
- citations.json: one entry for every dependency of every proof step, with its statement copied verbatim.
- report.md and searches.jsonl: this report and actual Q22 search records.

No new nodes and no new Mathlib leaves.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag, TateAlgebra, Tate algebra, restricted series, and separable cotangent. The algebraic separable-residue cotangent declarations do not state this analytic assertion. No Lean was written or compiled.

## Wanted literature

WANTED: Conrad, Several approaches to non-archimedean geometry, Theorem 1.1.5(1), PDF p.4, for lem-per-tate-separable-local-cotangent-coordinates; https://math.stanford.edu/~conrad/papers/aws.pdf. Read online, absent as an archival PDF in this read clone.

WANTED: Conrad, Irreducible components of rigid spaces, section 1.1 printed p.477 and Lemma 3.3.1 proof printed p.510, for lem-per-tate-separable-local-cotangent-coordinates; https://www.numdam.org/article/AIF_1999__49_2_473_0.pdf. Read online; these explain the imported regularity/separable-point motivation, not the explicit derivative formula.

WANTED: Temkin, Stable modification of relative curves, arXiv:0707.3953v3, Theorem 3.5.5 Step 2 printed p.22, for the source context of the existing tool lem-trf-affinoid-polynomial-closed-point-comparison. Its source field says Step 3, whereas the displayed completion comparison in the online PDF occurs in Step 2. https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf was read online. No cited existing node was edited.

## Findings and corrections

The item is true as stated. The imported source contains Tate regularity, but the explicit first-order coordinate map is an agent refinement. I retained every hypothesis, including finite separability and the zero-variable clause. The proof does not equate algebraic Kähler differentials of the Tate algebra with continuous differentials.

The latest blueprint chapter and unit differ from the historical imported records: their Fourier route is now stated through the curve heart. The ancestor's current Step 3 discusses duality and has no formal-algebraization sentence. I recorded this discrepancy in blueprint.from.place and split_report.blueprint, preserving the existing descendant route and the unit and chapter. The generic analytic and completion tools are declared in split_report.tool_uses; they replace no unit step.

The earlier unsplit item had no proof to retain. Existing upstream searches remain intact; the new Q22 searches are appended and exactly match searches.jsonl. The semantic hits concern algebraic presentation cotangent bases, one-variable formal Weierstrass preparation, or the definition of the local cotangent space. I read MvPowerSeries/Restricted.lean, RegularLocalRing/Defs.lean and Ideal/Cotangent.lean; none gives the item. The second semantic phrasing also gave only algebraic presentation results.

## Not duplicates

No new node is introduced. I reused lem-trf-affinoid-polynomial-closed-point-comparison instead of inventing Tate Noetherianity or completion comparison nodes. I reused the polynomial regularity/dimension, completion regularity/dimension, localization Noetherianity, and regular-local cotangent-dimension nodes. The existing lem-per-tate-rational-local-coordinates covers only rational points; I did not treat it as the finite-separable statement. Whole-blueprint searches for 'Tate algebra' and 'cotangent coordinates' returned no blueprint match; whole-DAG searches were read by statement rather than by incidental words in histories.

## Review by Q22

I read Conrad's Theorem 1.1.5(1) online: it states regularity and Noetherianity of Tate algebras, dimension r at every maximal ideal, and finite residue degree. Conrad's 1999 p.477 explains the rational-point/base-extension route; p.510 explains why separable regular points are smooth after completion. I reconstructed a smaller first-order proof rather than claiming either source prints the displayed derivative isomorphism. I read Stacks algebra.tex at lemma-dim-affine-space (00OP), proposition-finite-gl-dim-polynomial-ring (00OQ), lemma-Noetherian-permanence (00FN), the discussion at definition-regular-local (00KU), and more-algebra.tex at lemma-completion-regular (07NY) and lemma-completion-dimension (07NV). These are the exact source labels used by the existing tools. There is no new statement-only node needing a separate source review.

Step 1 uses only the localization definition, whose statement explicitly supplies the local ring and its maximal ideal. The residue formula and its kernel are proved from the fraction relation, including clearing factors; they are not assumed from a definition of the residue field.

Step 2 uses the statement of lem-trf-affinoid-polynomial-closed-point-comparison at J=0: it explicitly says C is Noetherian, the polynomial inverse-image ideal is maximal, and the induced local map induces an isomorphism of completions. The hypotheses on F and the restricted-series algebra are precisely ours. I opened that node and read its statement and its existing proof: I take no extra flatness, residue-field, or derivative conclusion from it. Localization Noetherianity gives Noetherian R; polynomial regularity gives regular local A; the polynomial maximal-localization dimension node gives dimension r, under maximality already established. Both completion nodes require Noetherian local rings, now established for A and R. Regularity transfers through the isomorphic completions; dimension transfers by the two equalities. These generic tools are documented individually in split_report.tool_uses.

Step 3 checks restrictedness and Leibniz directly, using the norm bound on integer coefficients and finite coefficientwise product sums. This does not invoke analytic differentiation, exchange of infinite sums, a Taylor theorem, a coefficient-field section, or a continuous-differentials comparison. The localization derivation formula is verified by differentiating the actual clearing relation, so a hidden extension theorem is unnecessary. Step 4 checks vanishing on every product of maximal-ideal elements, scalar linearity, and the precise numerator-only formula. These are elementary coefficient and fraction calculations; no hidden independent lemma is being moved into a long step.

Step 5 uses separability exactly where it is needed: f_i'(a_i) is nonzero. Since f_i(x_i) lies in the actual ideal n, its class exists in p/p^2. Its derivative vector has only the ith component, and that component is invertible in kappa. Thus all coordinate vectors have preimages. No assertion that the residue field is generated by the coordinates, and no equality of polynomial and analytic residue fields, is needed. Step 6 uses the full statement of lem-weil-pbc-regular-local-cotangent-dimension: finite-dimensionality and equality of cotangent dimension with dim R for regular local R. The basis argument proves injectivity from the dimension r and surjectivity, without an uncited substantive comparison. All step citations have verbatim statement quotes in citations.json. Every step is below 2000 characters.

Small cases: r=0 reduces to the field and zero cotangent spaces. For r=1 with a separable non-rational residue coordinate, its minimal polynomial supplies the unique nonzero tangent direction. In positive characteristic, a polynomial x^p-c with inseparable residue has zero derivative, showing exactly why the separability assumption cannot be dropped from the coordinate isomorphism. Boundary norm-one coordinates cause no problem because differentiation uses bounded integer coefficients, not topological nilpotence. No completeness assumption on the discrete local ring R is used: only its maximal-ideal completion is compared in Step 2.

Against delivery-errors B through E: no new nodes means no statement-only or duplicate packaging issue; every existing notion cited by the statement has its defining node, and TeX is retained unchanged. All non-elementary inputs are actual cited statements, the tools are declared, and the source labels were read. The proof has substantive calculations rather than relabelled clauses or one catch-all new lemma. No added hypothesis, wrong fibre or residue object, unsupported transport, cycle introduced intentionally, or SGA route is present. The remaining source-archive request and blueprint provenance discrepancy are reported above rather than concealed.

## Unfinished work

None in this one-level split. Existing dependencies retain their own independent work states. Remote dry run and push are the final mechanical verification steps.
