1. Files written

- `dag/nodes/sec-curve-estimates/lem-sc-pic-lift-closed-immersion-dim-le-one.json`: item split into four steps; no Mathlib leaf.
- `dag/nodes/sec-curve-estimates/lem-sc-noetherian-cohomology-vanishing-abelian-dim-one.json`: corrected statement-only node; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-cohomology-closed-immersion-pushforward.json`: self-contained statement-only node; no Mathlib match.
- `dag/nodes/sec-curve-estimates/def-sc-topological-abelian-cohomology.json`: new definition node; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-picard-h1-restriction-compatibility.json`: new compatibility node; no Mathlib match.

2. Attachments

- `thm-sc-hilbert-90` supplies the general Picard/H^1-of-units identification used for Stacks 09NU.
- No Lean declaration states the item exactly; the source grep for the item id and its key phrases returned no declaration.

3. WANTED:

- `literature/stacks-project/varieties.tex`, Lemma 09NY and its proof, because the Stacks TeX source is not present in this repository (the proof was checked against the read-only source checkout).
- `literature/stacks-project/cohomology.tex`, Proposition 02UZ and Lemma 02UV, for the same reason.

4. What was wrong in the imported node

The imported item had the correct Lemma 09NY statement but its supporting nodes incorrectly restricted cohomology to O_X-modules, used a non-definition of Noetherian topological space, and left closed-immersion pushforward undefined. I corrected those statements and added a statement-only compatibility node because Hilbert 90 alone does not identify the induced H^1 map with pullback of line bundles.

## Review by F1

I read the returned item and all three existing node statements, plus the source passages for Stacks 09NY, 02UZ, 02UV and 09NU (the repository's Stacks TeX is absent, so the source locations are recorded explicitly). The new definition states derived global sections and the long exact sequence for arbitrary abelian sheaves and identifies the scheme case with Zariski cohomology. The vanishing node now uses the exact minimal-closed-subset definition of Noetherianity. The pushforward node defines both the topological closed embedding and i_* sectionwise. The compatibility node states that the 09NU/03P8 torsor map sends L to i^*L, fixing the prior unsupported 'therefore'.

Step 1 follows the opening exact sequence in 09NY and uses the closed-immersion definition. Step 2 cites the corrected 02UZ specialization and the new cohomology definition; its hypotheses are exactly the item's Noetherian and dimension assumptions. Step 3 cites the self-contained 02UV statement with p=1 and F=O_Z^*. Step 4 cites Hilbert 90 and the new compatibility statement, so the surjection is genuinely the Picard pullback map. I checked identity and empty closed immersions and zero-dimensional Noetherian spaces; the corrected hypotheses remain meaningful in each case.

5. Incomplete work

The three supporting statements remain unsplit queue nodes. Their Stacks TeX sources are unavailable under this repository's `literature/` tree; the report records the cited source locations rather than claiming local copies.
