Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-ample-square-zero-thickening.json`: repaired split statement node; Mathlib searches remain no match.
- `dag/nodes/sec-curve-estimates/lem-sc-boundary-derivation-square-zero.json`: repaired unsplit statement for 0B8S; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-section-affine-open-kills-cohomology.json`: repaired unsplit statement for 01XR; no Mathlib match.
- `citations.json`: verbatim statement excerpts for every cited proof dependency by step.

Attachments: none. WANTED: none.

The earlier step 1 wrongly claimed support from the counit node while citing no node at all. The repair cites the quotient, annihilated-module, and affine cohomology statements directly. The earlier account also omitted the graded ring construction, the hypotheses of 01XR and 01YQ, and both clauses of ampleness; these are now explicit. No Lean was changed or compiled. The two supporting nodes remain unsplit at this stage.

## Review by F1

I read Stacks Cohomology of Schemes Lemma 09MS (`coherent.tex`, label `lemma-ample-on-reduction`) against the item: closed immersion, Noetherian X and Z, invertible L, and ample restriction are exactly its square-zero case. I read 0B8S (`cohomology.tex`, `lemma-boundary-derivation-over-cup-product`) and 01XR (`coherent.tex`, `lemma-section-affine-open-kills-classes`) against the new statements. The 0B8S node specializes its sheaf-of-rings statement to commutative O_X-algebras so its cohomology uses the cited scheme-module notion; it states explicitly why the kernel is an O-module. The 01XR node now introduces every notion with its definition citation and spells out the map called multiplication by s^e. Both nodes have statements only. Their zero-ideal/zero-class cases give zero boundaries or immediate annihilation; for 01XR, s=1 and X_s affine reduces to affine cohomology vanishing. I rechecked the recorded DAG, blueprint, Lean-source, and three-kind Mathlib searches; no duplicate theorem was found.

Step 1 uses the actual statements of `lem-weil-pbc-closed-immersion-unit-quotient` (the quotient is j_*j^*L^n), `lem-weil-pbc-closed-immersion-pushforward-annihilated` (2) (G_n is quasi-coherent and j_*G_n=M_n), and `lem-weil-pbc-affine-morphism-cohomology-edge` (H^1 comparison for affine j). Local freeness of L^n makes tensoring exact; I^2=0 annihilates M_n. It does not use the counit-only 01QY node or a homeomorphism claim. These three off-unit nodes are declared as generic tools.

Step 2 uses `lem-weil-pbc-quasi-coherent-ideal-zero-set-affine` to see V(I)=X, `def-weil-pbc-ample-invertible-module` to choose n>=1, s and affine Z_s, and the affine edge statement from step 1 to locate the obstruction on Z. Step 3 uses the exact sequences of step 1 and `lem-sc-boundary-derivation-square-zero`: the graded direct sums are commutative algebras locally modeled by a polynomial algebra, their kernel squares to zero, and naturality for degree inclusion and projection gives the degree-n boundary. The Leibniz induction is written in the step rather than hidden in a tag.

Step 4 checks each hypothesis of `lem-sc-section-affine-open-kills-cohomology`: Z is quasi-compact from Noetherianity and quasi-separated by `lem-weil-pbc-locally-noetherian-quasi-separated`; j^*L^n is invertible; Z_s is affine from step 2; G_n is quasi-coherent from step 1; p=1. The class is transported by `lem-weil-pbc-affine-morphism-cohomology-edge`, and naturality of that edge map for f -> f tensor s^e identifies the power action. The resulting zero boundary lifts the power of s.

Step 5 uses `def-weil-pbc-ample-invertible-module` for the stalkwise nonvanishing locus, `lem-weil-pbc-proper-fp-permanence` (b) for base change of a closed immersion, `lem-weil-pbc-closed-immersion-finite` for finiteness, and `lem-weil-pbc-quasi-coherent-ideal-zero-set-affine` for surjectivity because I is nilpotent. The affine source is Z_s. The target open is locally Noetherian and quasi-compact as an open of the Noetherian space X, which is the Noetherian hypothesis spelled out in `def-weil-pbc-scheme-conventions`. All four inputs to `lem-weil-pbc-finite-surjective-affine-target-noetherian` are therefore checked. Step 6 checks quasi-compactness of X and the positive exponent (e+1)n before applying both clauses of `def-weil-pbc-ample-invertible-module`.

For the return, I corrected points 1-4 in the proof, points 5-6 in the new-node statements and dependencies, and point 7 here. The proof's off-unit citations are declared in `split_report.tool_uses`; each cited node's statement was opened and its exact usable text is recorded in `citations.json`.
