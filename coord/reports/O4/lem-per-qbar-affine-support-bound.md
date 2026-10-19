# N4: lem-per-qbar-affine-support-bound

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-qbar-affine-support-bound.json`: statement, split into eleven proof steps; statement and statement dependencies unchanged. Mathlib searches found no exact match or one-line specialization.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- No new DAG nodes, no Mathlib leaves, no unit or chapter changes.

The other sandbox files are the source extracts, the cited-statement reading packet, the genuine `searches.jsonl` produced by msearch, and the scripts used to write this delivery. They are not project changes.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` for the item id, affine/support combinations, the perverse operations, and relevant pro-etale operations. There is no declaration stating this adic sheaf estimate. The nearby `AlgebraicGeometry.Etale.DerivedCategory.isPerverseLE_lowerShriek` and `isPerverseGE_lowerShriek` in `SixFunctors/Etale/Perverse/Operations.lean:199–223` contain `sorry`, have finite coefficients and compact-support conclusions, and are not attachments. Master source was not treated as proof evidence.

## WANTED

None. All sources used are already in `literature/`.

## What was wrong or missing

The item was an unsplit helper, with no proof. Its statement is true and has not been changed. In particular, its support is the **closure** of the nonzero adic fibre locus, not Stacks' possibly nonclosed support. The proof must justify this distinction.

A direct invocation of Stacks 0F0X on the given Qbar-ell sheaf would be a coefficient error: its statement is for torsion abelian etale sheaves. A first derived reduction of an integral heart representative can have a degree-minus-one Tor sheaf. Ignoring that sheaf would leave a gap. Also an arbitrary integral representative can have torsion supported outside the rational support; one cannot simply assign it the rational support dimension. Steps 2–3 construct a representative on the actual closed support, and Steps 4–6 keep both cohomology sheaves of its derived reduction.

The original ancestor blueprint's compact-support block argument has the problems already documented in the reviewed parent split. This delivery supplies the parent's existing affine ordinary-direct-image helper, using precisely the finite Artin estimate explicitly named in the ancestor's opening Stacks paragraph and the BBD 4.1.1 sheaf estimate. It changes neither the Fourier unit nor its route and does not introduce a new compact-support argument.

## Unfinished work

None for this stage-1 item. The reused input nodes retain their existing states; their proofs are not claimed as newly finished. No Lean was written or compiled.

## Searches and reuse

I read the chapter, the unit `sk-p-dl-a1-perverse`, the current main-20261015 ancestor statement/proof, and the reviewed parent node. I searched the full DAG by support, affine vanishing, generic base change, integral reduction/fibres, closed support, direct-image comparison and the tag 0F0X. I used `tools/blueprint_refs.py ancestor` and whole-blueprint searches for `affine support`, `integral reduction fibres`, `affine`, and `support bound`. The first two returned no matches; the broader results supply no duplicate of this adic sheaf statement. The existing `lem-kun-affine-direct-image-support-bound` supplies exactly the torsion estimate, and `lem-a1-integral-constructible-reduction-fibres` supplies exactly the finite-module fibre comparison that would otherwise need a new node. No nodes were created.

I ran and read two LeanFinder phrasings, two Loogle queries, two grep searches and LeanSearch through msearch. Their exact queries and returned names are appended to the item's retained inherited search history and recorded in `searches.jsonl`. Results concern affine inverse limits, algebraic etale loci, Artinian schemes and ideal-sheaf support. None concerns adic constructible sheaf higher direct images. No unavailable service was treated as evidence of absence.

## Not duplicates

No new nodes. The item and `lem-kun-affine-direct-image-support-bound` differ in coefficients and support conventions: the existing node treats torsion abelian sheaves and the pointwise transcendence-degree locus; the item treats the standard Qbar-ell heart and closed Zariski support. Steps 4–10 prove the passage between those assertions instead of declaring them identical.

## Review by N4

I read BBD 4.1.1 on printed pages 102–103, including its reduction to the sheaf inequality d(R^i f_*F) <= d(F)-i, and the local source of Stacks 0F0X (`etale-cohomology.tex`, `lemma-interlude-I`). I read Bhatt–Scholze 5.4.3 (bounded-below comparison), 6.6.11 (stratified perfect models), 6.7.2 with its reduction-comparison proof, and 6.8.2, 6.8.10–6.8.14 and Remark 6.8.15 (coefficient restrictions, integral/rational hearts and realization). I also checked the local Stacks statements 0B1C (`varieties-item-dimension-irreducible-trdeg`), 00DV (`algebra-lemma-NAK`), the reduced induced closed-subscheme construction, 09BM and 09AH (closed/open exactness), the geometric-stalk exactness lemma, 01S7 (affine morphisms are qc and separated), and 05SE (right derived functors are triangulated). I read the current two-term uniformizer node and its main-20261015 proof. There are no new nodes requiring separate source reviews.

I opened every node cited by the eleven steps and read its **statement**, not merely its proof or title. `citations.json` records the actual clauses used. The checks by step were as follows.

1. `lem-weil-pbc-finite-type-over-noetherian` applies to a finite-type scheme over the noetherian field k, and `lem-kun-dimension-finite-type` supplies finite dimension. `lem-per-adic-heart-pullback-fibres` explicitly supplies common finite-stage heart objects, the normalized fibre extension and finite-stage cohomology; `prop-weil-localized-tstructure` explicitly says that the rational heart is the essential image of the integral heart. Thus H exists in degree zero. Faithfulness of extension of vector spaces proves equality of the nonzero loci, rather than merely containment.

2. `lem-weil-pbc-reduced-induced-closed-subscheme` provides the actual i:Z→X. `lem-weil-pbc-continuous-coefficients-immersion-restriction` identifies the coefficient sheaves under i and j. `lem-weil-pbc-proetale-ringed-open-closed` says that i_* is exact, that restriction back to Z is the identity and that the complementary restriction vanishes. The resulting finite-module local models certify membership using `lem-weil-pbc-integral-stratified-perfect-characterization`, whose statement includes the compatible etale-origin witnesses. I did not use proper base change or generic base change here.

3. `lem-per-continuous-rational-derived-realization` is an equivalence with the continuous coefficient module realization, is t-exact and commutes with locally closed restriction. `lem-per-adic-heart-pullback-fibres` detects the zero restriction on U. The **statement** of the ringed open-closed lemma gives both the short exact sequence and filtered-colimit commutation for i_*; X is qcqs. Localization is the sequential sheaf colimit, so these clauses identify the two realized objects. Full faithfulness then gives QK≅F_E. This checks the supported-model argument rather than assuming a lattice with the desired support.

4. `det-pe-derived-nakayama-resolution` supplies the uniformizer cone over the continuous completed coefficient sheaf, with its finite constant quotient. The kernel/cokernel clause of `lem-weil-heart-short-exact-triangles` gives the cohomology in degrees -1 and 0. `def-weil-pbc-bounded-constructible-complete` actually includes an etale-origin witness L_1, so no theorem is inferred from a definition of flatness or constructibility. Exact comparison from `sk-thm-pe-direct-image-comparison` and full faithfulness from `thm-weil-pbc-site-comparison` identify the cohomology and reflect its vanishing on U. T and G are both finite-coefficient module sheaves; both have torsion underlying abelian sheaves.

5. `lem-sc-closed-irreducible-dimension-trdeg` identifies the dimension of the closure of each point of Z with its residue transcendence degree. Its ambient finite-type hypothesis holds. Monotonicity for a closed subspace follows directly from chains. `lem-kun-affine-direct-image-support-bound` explicitly gives the two needed estimates for every r≥0. Its affineness, finite-type and torsion hypotheses all hold. `lem-sbc-higher-direct-image-forget-comparison` is the theorem identifying higher module direct images with their underlying abelian counterparts, not just a definition of the forgetful functor.

6. The truncation and cohomological-functor clauses of `lem-weil-heart-short-exact-triangles` apply to the ordinary derived category. I added `lem-weil-pbc-derived-direct-image-triangulated` to justify applying Rf_* to the triangle. `prop-weil-pbc-geometric-stalks-exact` then gives the support containment from the displayed three-term exact segment. The T[1] term contributes R^{q+1}f_*T, with the stronger support bound a-q-1; the sign was checked explicitly.

7. `lem-sf-integral-direct-image-constructible` states both output constructibility and the reduction isomorphism. It holds for finite-type schemes over the arbitrary field k with ell invertible; no finite-field hypothesis was inserted. `lem-weil-pbc-affine-morphism-permanence` supplies qcqs for `sk-thm-pe-direct-image-comparison`. `prop-weil-pbc-integral-tstructure` keeps N_q in the integral heart. The uniformizer cone and long exact sequence give N_q/pi N_q→H^q(M_1) as a monomorphism even when N_q has torsion. `lem-a1-integral-constructible-reduction-fibres` explicitly says this **ordinary quotient** is of etale origin. The exact fully faithful comparison reflects the monomorphism between the two etale-origin sheaves. No claim that geometric stalks commute with an arbitrary inverse limit is needed.

8. Stalk exactness applies to that etale monomorphism. `lem-a1-integral-constructible-reduction-fibres` supplies a finitely generated A-module P_y, identifies its residue quotient with the quotient sheaf's etale stalk, and identifies its rational fibre. These are exactly the hypotheses of `lem-weil-pbc-nakayama-local-generators`, with N=0 and the maximal ideal generated by pi. `prop-weil-localized-tstructure` commutes localization with cohomology. `prop-weil-pbc-rational-transport` applies because Step 7 supplies the integral constructible direct-image functor. Thus this step concludes a rational fibre vanishes from a finite residue quotient, with no unproved continuity assertion.

9. `prop-weil-pbc-scalar-extension` explicitly compares ordinary direct image under finite coefficient extension. `lem-per-adic-heart-pullback-fibres` computes cohomology and fibres at common stages and states that the nonzero locus is constructible. These clauses give the intended Qbar-ell object and the same nonzero locus.

10. This is elementary topology once `lem-sc-closed-irreducible-dimension-trdeg` is available: a finite locally closed decomposition of a constructible set shows each generic point of its closure belongs to the set. The pointwise E_b bound applies at those generic points, and the cited dimension formula bounds each closed component. The finite union has the maximum component dimension by the definition using irreducible chains. For b<0 the set is empty. I expressly checked that this reasoning is false for arbitrary nonconstructible subsets, so constructibility has been retained.

11. `lem-per-qbar-ordinary-adjunction` gives an actual ordinary direct-image adjunction on the arbitrary-field common-stage constructible categories. Its separated finite-type hypotheses follow from affineness and the item. `lem-per-adic-heart-pullback-fibres` makes pullback triangulated and preserves the heart; bounded truncations and extension closure from `lem-weil-heart-short-exact-triangles` therefore preserve the negative class. Orthogonality kills the map from the negative truncation to Rf_*F; that map is an isomorphism on every negative cohomology object, which forces these objects to vanish. This uses the standard t-structure, not the perverse one.

All off-unit proof inputs are declared in `split_report.tool_uses` as generic tools, with the particular needed clause. They do not replace a step of the Fourier exactness unit. I checked the full dependency closures of the principal comparison and realization inputs for a path back to this item; none reaches it.

Small cases checked: F=0 and empty X; q=0; q>a; the identity morphism; a punctual sheaf; and the open affine immersion G_m→A^1 over an algebraically closed field, where R^1 has boundary support of dimension zero and the a=1,q=1 bound is sharp. For negative q the adjunction proof applies independently of the reduction argument. Integral torsion is deliberately allowed, and the example K=A/pi in degree zero checks that K_1 has both degree -1 and degree 0 terms. A representative enlarged by a torsion sheaf outside Z checks why Steps 2–3 are needed.

Against delivery-errors B–E: no new statement-only or Mathlib-leaf metadata is needed, no node duplicates or item-clause wrappers were created, all substantive external results are cited as node statements, all coefficients and scheme hypotheses were checked above, and the proof contains the coefficient argument rather than relabelling the goal. Every step is shorter than 2000 characters. I corrected two initially implicit citations during self-review: triangulatedness of finite Rf_* and qcqs/separatedness of affine morphisms. No source statement, target statement or item hypothesis required correction.

## Validation

The server `check_dag` passed before the final report. Final delivery dry-run and push results are recorded by the delivery tool.
