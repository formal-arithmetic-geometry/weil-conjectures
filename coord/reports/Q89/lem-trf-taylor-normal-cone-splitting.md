# Q89 stage-1 worker report

Item: lem-trf-taylor-normal-cone-splitting. Date: 2026-10-22. Direct delivery, with self-review below.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-taylor-normal-cone-splitting.json: statement item split into ten steps; no new nodes and no new Mathlib leaves. The mathematical statement is unchanged. The missing associated-graded notion dependency is supplied explicitly.
- citations.json: one entry for each cited node in each proof step, with its statement copied verbatim. These quotes were generated from the actual repository node files, not reconstructed from their proofs.
- report.md: this report. searches.jsonl contains the five fresh searches produced by msearch.py; the item's earlier Q76 search records are retained in its JSON. write_split.py is sandbox-local preparation material only.

## Attachments

None. Searched the exact blueprint docstring tag and the item id, and Taylor/normal-cone/associated-graded terminology in lean/WeilConjectures. No declaration states the whole item. The private first_order_expansion in RingTheory/PopescuDesingularizationSubstitution.lean:30 only treats the first-order expansion of a polynomial over an arbitrary ring, not local completion, nonclosed residue directions or ideals in the Taylor power-series ring.

## WANTED

None for this proof: the local-algebra sources used are available in literature/stacks-project. BM 1997 Definition 3.4 and the opening of Theorem 9.6 remain the inherited motivation, not an unverified theorem used in this split. The ideal comparison is expressly an agent argument, not attributed verbatim to Stacks 0C35 or 0C0S.

## Audit and changes

The repository item was unsplit; the sandbox had no earlier item, proof, report or search log. I retained the original statement, source, creation record, blueprint ancestry and old searches. No statement dispute was found. There is no new definition, no Lean writing and no compilation.

The essential issue is the map on residue-field coefficients. For a nonclosed point, the compatible coefficient section L -> S coming from the completion of R need not be the constant L inside the displayed Taylor ring. I kept these sections distinct. They agree only on residues, which suffices to make the graded comparison L-linear. No claim identifies the entire completed local ring of M at a nonclosed point with the n-variable Taylor ring: its own completion has c variables, and the other s variables arise from the closed fibre of R -> O_(M_L,a_L).

The input lem-trf-smooth-local-tangent-cone-extension was considered and not used: its statement assumes essential finite type over Q, which need not hold for an arbitrary characteristic-zero base field k. Instead the existing relative-Cohen node has no finite-type restriction on its Q-algebras. I also considered lem-trf-smooth-rational-point-completion; rather than add finite-generation/separability and essential-smoothness infrastructure, step 2 proves directly the lifting property needed by the existing formally-smooth local-map theorem. That proof uses the exact characteristic-zero field-extension lifting statement, not merely a definition of smoothness.

The four off-unit theorem uses are recorded in split_report.tool_uses. They supply generic regularity, flatness/fibre structure, Noetherian power-series rings, and preservation of regularity by completion. The two relative/absolute coordinate theorems already belong to this unit. These tools refine the inherited lower local-algebra branch; they do not substitute for the current blueprint's contracting-correspondence argument.

## Searches and reuse

DAG searches covered tags 0C35, 0C0S, 07NQ, coefficient fields, complete regular local coordinates, tangent-cone extensions, local completions, cotangent dimension, Nakayama, and initial ideals. Opened and read the exact statements of every dependency used. Whole-blueprint searches with tools/blueprint_refs.py covered Taylor, normal cone, regular local, power series and field extension. The ancestor command confirms lem-trf-local-term-locality, and the existing via chain is retained. No blueprint node states this full Taylor ideal comparison; same_as remains empty.

Fresh msearch.py searches used LeanFinder twice with distinct formulations, Loogle on MvPowerSeries and Ideal, LeanSearch on initial forms of extended ideals, and grep in RingTheory. All five services returned successfully. Inspected the returned types: the closest Loogle hits concern the ideals of allowed evaluation/substitution families and truncation congruences, not initial ideals of an extended local ideal. LeanFinder returned smooth-locus/cotangent machinery and univariate Weierstrass preparation; LeanSearch returned fractional ideals, an initial functor for local cohomology, and ordinary ideal maps. The grep hits are polynomial Taylor manipulations. None is an exact theorem or a one-line specialization proving this item. The actual query strings and unmodified logged result summaries are in the JSON, alongside the inherited searches.

## Not duplicates

No new nodes. Reused lem-trf-relative-cohen-flat-presentation and lem-trf-regular-complete-coefficient-coordinates instead of creating a Taylor-specific restatement of either. The former gives compatible completed local presentations for a flat local map with regular closed fibre; it does not assert this initial ideal comparison. The latter gives coordinates over a specified coefficient section; it does not compare two local rings or their ideals.

## Review by Q89

I read the standing brief, stage-1 document, worker role, GOAL.md, the three levels in SETUP.md, the chapter and unit records, and delivery-errors B--E in both copies. I read the current ancestor's blueprint_update, which uses contracting correspondences, and retained this item's narrower historical lower-input provenance. The item is not the unit key statement, so no unit realization fields are changed.

Sources opened for the mathematical proof were algebra.tex Tags 0322 (proposition-characterize-separable-field-extensions), 00FN (lemma-Noetherian-permanence), 00DV (lemma-NAK), the discussion before 00KU (definition-regular-local), 05GG (lemma-hathat-finitely-generated), 0C0S (lemma-regular-complete-containing-coefficient-field), and the neighbouring 032C power-series remark; more-algebra.tex Tags 0C35 (lemma-power-series-over-residue-field), 07NQ (proposition-fs-flat-fibre-fs), and 07NY (lemma-completion-regular); varieties.tex Tag 056S (lemma-smooth-regular). There are no new nodes whose statement/source pairing needs separate review. I did not use an SGA source.

1. Step 1 uses def-weil-finite-type-morphism to choose a finitely generated affine coordinate algebra, and def-weil-pbc-localization-at-prime for local rings. lem-weil-pbc-finite-type-algebra-noetherian and lem-weil-pbc-localization-noetherian state precisely the two permanence assertions used for C and C tensor L. Both base fields are Noetherian since their only ideals are zero and the unit ideal. lem-weil-pbc-smooth-scheme-over-field-regular explicitly gives regularity of every local ring; no closed-point or algebraically-closed-field assumption was added. The affine residue homomorphism is written explicitly, so the identity L -> L is checked rather than assumed from an arbitrary base change point.

2. Step 2 uses lem-weil-pbc-char-zero-field-extension-formally-smooth exactly for its square-zero lifting property, and def-weil-pbc-formally-smooth-adic exactly for the lifting condition required later. I wrote the tensor pairing and denominator-unit calculation, which proves the needed base-change/localization lifting in this case. The target carries its already fixed R-structure, so the lift remains R-linear. No smoothness theorem hidden in the definition is invoked.

3. Step 3 uses the statement of lem-weil-pbc-fs-adic-flat-geometrically-regular-closed-fibre for flatness and geometrically regular closed fibre; it actually states both conclusions. Identity base extension gives regularity of F. The regular-local cotangent-dimension statement ensures its finite dimension, so the finite-dimensional closed-fibre hypothesis of lem-trf-relative-cohen-flat-presentation holds. R and D are nonzero Noetherian local Q-algebras by step 1. Both residue fields are the same specified L. The relative-Cohen statement explicitly supplies sections compatible with the completed map, not just unrelated ring isomorphisms. I renamed its presentation ideal H to distinguish it from the arbitrary ideal I of the item.

4. Step 4 uses only the Noetherian assertion for a power-series ring over a field in lem-weil-pbc-power-series-field-cohen-regular-complete and the coefficient definition of def-weil-pbc-multivariate-power-series. The quotient calculation is written, including why an infinite family of coefficients still yields a finite ideal expression: H has a fixed finite generating list. It needs no assertion that an arbitrary tensor product commutes with infinite products. This is an elementary finite-generator coefficient calculation, not a new theorem node.

5. Step 5 checks all hypotheses of lem-trf-regular-complete-coefficient-coordinates. lem-weil-pbc-adic-completion-noetherian supplies Noetherianity; lem-weil-pbc-local-completion-local-ring supplies the maximal ideal and residue field; lem-weil-pbc-module-completion-complete supplies completeness; lem-weil-pbc-completion-regular-local supplies regularity. lem-weil-pbc-adic-completion-mod-power identifies the first two jets. lem-weil-pbc-regular-local-cotangent-dimension then identifies the dimension as c; lem-weil-pbc-nakayama-local-generators applies to the finite maximal ideal to verify that this exact list of z_j generates it. The coefficient field is the section alpha actually supplied in step 3. Thus both the number and choice of parameters meet the coordinate theorem's statement.

6. Step 6 uses the power-series and polynomial definitions for the monomial calculation and the associated-graded definition for its multiplication. I included a finite partition of monomials by degree-q divisors to justify the converse description of a maximal-ideal power. The completion-mod-power theorem is the statement that transports these finite jets from A back to R. The inverse of Psi is a local-ring isomorphism, so the linear change on the full tangent space is invertible. Although Psi need not fix the constants in S, it fixes their residues, so the graded map is L-linear. This proves independence for the actual Taylor linear forms, not for some arbitrarily chosen set of normal coordinates.

7. Step 7 uses just the associated-graded multiplication and the coefficient formula for power-series multiplication. It calculates the degree-q part explicitly and includes the possible zero part; it does not replace degree-q by the lowest nonzero degree without justification. The ideal property of J is proved with representatives. No assertion about the proof of another node is used.

8. Step 8 uses precisely the surjectivity and kernel statement of lem-weil-pbc-adic-completion-mod-power. All finitely many coefficients a_i of an element of IA are approximated in the same quotient A/(mA)^(q+1). Contraction of that power is m^(q+1), so the approximating g belongs to m^q when h does. This treats arbitrary I, including I=R, and proves agreement of the degree-q subspaces, stronger than just saying completion preserves orders. There is no unquoted exactness-of-completion assertion.

9. Step 9 is the explicit finite-generator coefficient argument of step 4 applied to K=IA, followed by one finite sum for a homogeneous component. It uses the power-series and polynomial definitions only, in addition to the preceding proved steps. The condition h_nu in (Z)^(q-|nu|) follows coefficientwise from the absence of lower total degrees; it is not an invalid assertion about the order of a sum with cancellation. Conversely monomials times initial forms of elements of K generate the extension ideal, which gives the reverse inclusion. No standalone non-elementary comparison is left hidden.

10. Step 10 uses the polynomial universal property to identify the image ideal under the explicitly determined graded isomorphism. Associativity of ideal extension is a finite-sum calculation. The c=0 deduction uses the actual local-generators statement of Nakayama on the finite maximal ideal. There is no assumption that c=n, nor that a is closed.

Small cases checked against the formulas: a closed separable point (s=0); the generic point of A^1_k, where c=0 but the Taylor ring still has one variable; the generic point of y=0 in A^2_k, where R=k(x)[y]_(y), c=1 and Taylor expansion also has the x direction; I=(y^2), I=0, I=R; and n=0. In the third example coefficients such as x expand as x+T_x, demonstrating why the compatible coefficient section cannot be treated as constant. The initial ideal for (y^2) is nevertheless (T_y^2), exactly as the coefficient calculation predicts.

B1--B9: no new unsplit statements, missing notions or duplicate nodes were introduced; JSON uses ordinary TeX escapes; blueprint ancestry and searches are preserved. C1--C8: non-elementary inputs are exact cited statements with verbatim quotes, and off-unit tools are declared. D1--D5: the item carries the proof, including both inclusions of the initial-ideal identity, rather than delegating a clause to a new node. E1--E7: hypotheses, coefficient maps, localizations and small cases are checked above. Each proof step is below 2000 characters. The server review_split check passed before the delivery dry run.

## Incomplete work

None at stage 1. The cited existing open nodes remain separate items; I did not split or alter them. Final server preflight/dry-run and push results are recorded below when available.
