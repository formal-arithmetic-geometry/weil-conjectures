# Worker report: lem-pur-coordinate-line-adjunction

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-coordinate-line-adjunction.json: statement, split into six proof steps; Mathlib verdict: no match. Statement and statement dependencies retained unchanged.
- citations.json: 27 exact statement excerpts, one for each node citation in each step.
- No new nodes and no Mathlib leaves. No Lean files written or compiler invoked.

## Attachments

None. Read-only searches under lean/WeilConjectures found no declaration with the item's blueprint tag. Searches for affine-line/affine-space adjunction and trace found the generic affine-space smooth-duality induction, which assumes the affine-line duality and does not state the actual normalized counit, ordinary/pro-etale transport, or all the geometric clauses here. It is not an attachment. The generic Mathlib composite-counit formula was read at Mathlib/CategoryTheory/Adjunction/Basic.lean:580; it is only an ingredient, already represented by def-weil-pbc-composite-adjunction.

## WANTED

None. The current detailed blueprint proof and the projective-line diagonal-kernel proof are present. This split expands their rank-one argument and is marked agent-written.

## Findings and corrections

The item was statement-only, created by the Q107 re-split of cor-pur-affine-space-zero-section-purity. No repair note for this item was present. Its statement is valid, including a=n at ramified coefficients: ell lies in the uniformizer ideal, so ell^n vanishes modulo varpi^n. No restriction e|n is required, and none was added.

The actual counit needs an argument, not just right-adjoint uniqueness: Step 4 writes the open counit/tensor identity and the proper projection naturality square. I revised this square to use forward proper projection maps before inversion, so the calculation does not assume an extra proper projection isomorphism at an open extension. Invertibility is used only for the specified compact projection (bounded constructible Tate line and finite-Tor K) and the projective projection supplied by the normalized P1 adjunction. The two tensor symmetries agree with the definition of gamma.

The underlying blueprint still cites thm-pur-affine-line-purity. Its current finite-level context is narrower elsewhere in the DAG; this split instead proves the required all-n assertion directly from the existing ordinary-finite P1 adjunction and site comparisons, exactly along the unit's projective-line/open-chart route. No smooth-purity theorem, zero-section purity, or SGA source is used.

## What could not be finished

Nothing in the stage-1 split remains open. Existing cited nodes retain their own independent stage states; they are not claimed proved here.

## Not duplicates

No new nodes were created. Whole-blueprint searches for “affine-line adjunction” and “normalized coordinate” found no exact imported node. The broader “coordinate” search was read against the parent and neighboring affine-space comparison, Thom, and orientation statements. Existing ordinary P1, etale-locality, compact projection, ordinary open tensor, and site-comparison nodes supply the reusable facts, so no specialized copies were made.

## Review by Q157

I read coord/delivery-errors.md B–E, SETUP.md's three-level rule, the chapter sec-smooth-purity record, unit sk-prop-an (especially its rank-one Step 5), the current main-20261015 cor-pur-affine-space-zero-section-purity.proof.md, and main-20261015 sec-six-functors-basics/sk-prop-geo-p1-adjunction/thm-amb-p1-adjunction.proof.md. The latter fixes the counit as normalized trace with projection formula via the diagonal-kernel route; the former instructs restriction to the affine chart and identifies gamma as the transpose. I also read Stacks 03PK/03PL (etale-cohomology.tex, section-kummer/lemma-kummer-sequence) and 0GL1/0E8I (sites-cohomology.tex and sites-modules.tex, lemma-j-shriek-and-tensor); the proof does not claim these alone give purity. There are no new nodes requiring a new source review.

Step 1: I opened the statements of lemma-nagata-relative-affine-space-open-immersion, lemma-nagata-projective-space-base-change-proper, lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type, and the three cited definitions. They give exactly the open chart, proper projection, Noetherian consequence and finite dimension used. The coordinate algebra argument proves separatedness of p, tower identities and universal Cartier property explicitly. It works over a ring with nilpotents; no field-domain argument is used for coordinate multiplication. Homogeneous-coordinate interchange aligns the chart lemma's D(T_0) with the comparison definition's D(T_1).

Step 2: lem-asd-etale-finite-twist-pullback states local rank one, all powers, arbitrary inverse-image compatibility and exponent comparison. lem-pur-vector-integration-site-comparison states comparison with the specified inverse-limit Tate line and independence of annihilating exponent at arbitrary n. These are statements, not constructions taken from their proofs. The coefficient conventions supply the DVR quotient, and the written ell=varpi b calculation checks the annihilator. Testing n=1 for ramified E gives the residue field, with ell=0, so this case is included. No flatness over Z/ell^a is required.

Step 3: lem-amb-etale-adjoint-locality explicitly supplies the termwise derived extension-by-zero adjunction on entire ordinary etale categories, not merely a sheaf adjunction. The chart is a quasi-compact open of the Noetherian projective line, hence separated etale finite type. lem-asd-ordinary-finite-p1-adjunction explicitly states Rq_* left adjoint to q* tensor L[2] and its actual counit for every finite annihilated ring and Noetherian base. def-amb-etale-compact-support names the left composite. def-weil-pbc-composite-adjunction explicitly gives its counit. The module inverse-image composition and derived tensor pullback statements provide the two displayed right-functor identifications; the twist pullback lemma supplies j*L_P=L_X. These comparisons descend the exact inverse-image functors, so no coefficient-line orientation is chosen anew.

Step 4: lem-pur-etale-open-derived-tensor is the ordinary-etale derived open tensor isomorphism with arbitrary complexes, and its statement specifies the sheaf-induced comparison. Under the open adjunction of the locality lemma, restriction and the open unit reduce its counit compatibility to the identity. I wrote that reduction, rather than assuming a hidden compatibility theorem. The normalized P1 lemma specifies its projection and counit. lem-weil-finite-compact-projection-formula explicitly identifies the compact map as proper projection followed by open tensor and states naturality. Its hypotheses hold for F|X=L_X[2] and finite-Tor K. The formula for gamma fixes precisely the two symmetries; shifts introduced by the line are even. The square now uses forward proper projection maps, avoiding any claim that extension by zero preserves constructibility merely to invert another projection map.

Step 5: thm-amb-etale-exceptional-adjoint gives the ordinary right adjoint for the compactification already checked, and def-weil-pbc-adjunction-conjugate states that conjugating an isomorphism of left adjoints gives an isomorphism of right adjoints. Applying it to identity has the stated transpose and counit equation. This preserves the normalization established in Step 4.

Step 6: the vector-integration site-comparison statement includes the actual open counit, projective trace, compact projection, transpose formula eta^p=C(eta^e), and exponent independence; it is strong enough for every comparison used here. The affine-line comparison definition specifies the same integration composite. det-pe-finite-tor-comparison-noetherian gives an equivalence for a qcqs base and discrete Noetherian ring, which applies to Noetherian T and finite A. Thus every pro-etale finite-Tor object has the required ordinary representative. The argument covers the empty base (all maps of zero objects), zero input, r=0, disconnected and nonreduced bases, every n>=1, and every allowed a.

I checked the dependency closure of every proposed proof ingredient for a path back to this item; none occurs. All 27 citation quotes were tested as literal substrings of the cited live statements. No proof step exceeds 2000 characters. Off-unit facts are declared as generic tools in split_report.tool_uses with their precise purpose; the proof keeps the unit's P1-adjunction then open-restriction route. Mathlib searches were executed through msearch.py in two semantic phrasings, with Loogle, LeanSearch and grep; the logged hits are affine algebraic geometry or unrelated/generic adjunctions, not this item. Existing inherited search records were retained as provenance and new executed records appended. No statement dispute or source correction was needed.

The first full dry run returned only citation-excerpt length failures (minimum 40 characters). I replaced the excerpts with each cited statement in full, so that the hypotheses and the complete portion used are visible without a short-quote ambiguity. No mathematical step or dependency changed in response.
