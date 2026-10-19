# Stage-1 report

1. Files written: item `lem-weil-pbc-condensed-point-basis-evaluation` (statement, 4 proof steps); `lem-weil-pbc-proetale-point-components-maps` (statement-only, Mathlib no match); `lem-weil-pbc-proetale-sheafification-wcontractible-sections` (statement-only, Mathlib no match).
2. Attachments: none.
3. WANTED: none.
4. No finished declaration with the item tag or exact statement exists in the source checkout. The source is the Bhatt–Scholze Lemma 4.2.13(1) computation, with the exact master explanation in `RefactorInstruction.tex`, Section 4. I checked the existing point-pullback node and the affine weakly-contractible covering nodes; neither states the finite-quotient component correspondence or the sheafification calculation, so these are the only new supporting nodes. The item keeps all hypotheses and conclusions unchanged.

## Review by NG

I read the item source in `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf` and the exact master `RefactorInstruction.tex` around the point-pullback lemma. Step 1 cites the new component/morphism statement, whose hypotheses introduce the scheme, pro-etale site, affine weakly contractible object, profinite parameter, and quotient topology. Step 2 cites the existing geometric inverse-image statement for the left Kan extension and the new finite-quotient correspondence; those statements provide exactly the construction and bijections used. Step 3 cites the new sheafification-on-the-basis statement, which explicitly gives the isomorphism needed at a weakly contractible affine and its naturality. Step 4 is the direct pointwise operation and quotient-topology check. I verified every citation quote against the node files and recorded them in `citations.json`. I ran all required Mathlib search kinds for each new node; LeanSearch was unavailable and recorded as such. No Lean files or compilers were used.

## Second reading by NG

- Item statement: checked against Bhatt–Scholze, Lemma 4.2.13(1), and the expanded point-evaluation proof in `RefactorInstruction.tex` Section 4; all scheme, pro-etale, profinite, weak-contractibility, quotient-topology, coefficient-kind, naturality, and operation clauses are retained, including empty and zero cases.
- Item step 1: checked the component/morphism construction against the statement of `lem-weil-pbc-proetale-point-components-maps`; its profinite quotient, continuous-map bijection, and both compatibilities are exactly what the step uses.
- Item step 2: checked against `lem-weil-pbc-profinite-point-pullback` and the component-maps node; the cited left Kan extension and finite-quotient correspondence supply the colimit calculation and naturality, with no use of a node proof.
- Item step 3: checked against the sheafification node; its stated canonical isomorphism and naturality justify passage from presheaf sections to sheaf sections on weakly contractible affines.
- Item step 4: checked directly from the preceding comparison and quotient-topology definition; pointwise ring operations are elementary, and no uncited non-elementary fact is used.
- New node `lem-weil-pbc-proetale-point-components-maps`: checked as a strict supporting fact against Lemma 4.2.13(1) and the finite-quotient inverse-limit argument; statement-only, self-contained, with scheme/site/universe dependencies and Mathlib searches recorded.
- New node `lem-weil-pbc-proetale-sheafification-wcontractible-sections`: checked against the weakly contractible sheafification clause of Lemma 4.2.13(1); statement-only, self-contained, and now explicitly defines weak contractibility and cites the point-pullback construction.
- Small cases checked: empty affine (unique maps and empty covering), a point over a field (component space a singleton), finite discrete profinite sets, and the zero/one operations for abelian-group and ring-valued coefficients.
- Changes made: corrected the item `created.item` metadata; expanded both supporting statements to define weak contractibility by surjectivity on sections; added `lem-weil-pbc-profinite-point-pullback` as the sheafification node’s dependency. These repairs enforce self-contained statements and accurate provenance without changing the mathematical claim.
