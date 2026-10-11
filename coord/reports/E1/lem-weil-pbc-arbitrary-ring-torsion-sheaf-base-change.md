# Stage-1 report

1. Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change.json`: repaired item, no new supporting node.
- `citations.json`: citations for all three proof steps.

2. Attachments: none.

3. WANTED: none.

4. What was wrong or incomplete: the returned node `lem-weil-pbc-torsion-module-injective-resolution` asserted a torsion-preserving injective resolution in `Mod(X_et, Lambda)`. This is false for non-noetherian Lambda (the reviewer supplied the square-zero extension counterexample), so that node was deleted. The original item also used the wrong IA hypothesis: Stacks Tag 0A4B, statement (2), assumes injectives of `Z/lZ`-modules. I repaired the item to assume coefficient-wise IA for injective `(Lambda/l)`-module sheaves. This is the E7 statement correction required by the return; the existing Lean declaration `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity` still has the broader arbitrary-Lambda IA statement and `sorry`, so it is not an attachment.

5. What I could not finish: the corrected statement is the mathematically valid Stacks route, but its Lean declaration must be updated separately by the maintainer to reflect the coefficient-wise IA hypothesis.

## Not duplicates

No new nodes were created, so no duplicate claims remain.

## Review by E1

I reread Stacks Tag 0A4B (`lemma-proper-base-change-in-terms-of-injectives`), including statement (2) and proof paragraphs 2-3. The source explicitly uses injective `Z/lZ`-module sheaves, filtered colimits `F = colim F[n]`, prime devissage, and an injective resolution only after reducing to a sheaf killed by one prime. I therefore removed the false arbitrary-`Lambda` torsion-resolution node and changed the item hypothesis to injectives over `Lambda/l`.

Step 1 cites the existing filtered-colimit theorem for higher direct images and the existing theorem that inverse image preserves all small colimits; their statements provide exactly the two commutations used. Step 2 cites the prime-torsion devissage statement, the five lemma, underived-exchange naturality, and derived-exchange naturality; these supply the exact sequences, the isomorphism criterion, and commutativity needed for induction. Step 3 cites enough injectives for module sheaves, the coefficient-wise IA hypothesis for pushforward acyclicity, Leray acyclicity, proper underived exchange, termwise derived exchange, and the forgetful-coefficients comparison. I checked each quoted sentence in `citations.json` against the cited node files.

The repaired proof avoids treating a `Lambda/l`-injective as a `Lambda`-injective and avoids treating a module-injective complex as a K-injective complex of abelian sheaves. Small cases checked were `F=0`, `n=1`, and a sheaf killed by one prime. No Mathlib declaration states this etale proper-base-change theorem; the recorded LeanSearch was unavailable and the Loogle, LeanFinder, and source grep searches found only generic infrastructure.

The return points were all addressed: the false resolution node was removed; the IA hypothesis was corrected to coefficient quotients; and Step 3 now cites only coefficient-module results applicable to the etale setting.

## Second reading by E1

- Item statement: checked hypothesis by hypothesis against Stacks Tag 0A4B, statement (2): properness, arbitrary base change square, prime-wise injective acyclicity over $\\Lambda/\\ell$, and torsion coefficient sheaf conclusion all match; tested $F=0$, $n=1$, and a field coefficient quotient.
- Step 1: checked against Tag 0A4B proof paragraph 2 and the statements of `lemma-weil-pbc-direct-image-filtered-colimit` and `lem-weil-pbc-inverse-image-preserves-colimits`; proper base changes are quasi-compact and quasi-separated, and the colimit exchange is exactly the cited result.
- Step 2: checked against Tag 0A4B proof paragraph 2 and the statements of prime-torsion devissage, the five lemma, underived naturality, and derived-exchange replacement; the induction and naturality requirements are stated explicitly.
- Step 3: checked against Tag 0A4B proof paragraphs 2-3 and the statements of enough module injectives, Leray acyclicity, proper underived exchange, termwise derived exchange, and forgetful-coefficients comparison; the coefficient-wise hypothesis supplies the required $f'_*$-acyclicity directly.
- New supporting nodes: none; the only delivered node is the item statement itself, and it has its definitions, source tag/label, blueprint fields, and recorded Mathlib searches.
- Removed the unrelated `lem-weil-pbc-injective-module-abelian-acyclic` and `lem-weil-pbc-module-pushforward-injective-acyclic` citations: the latter concerns $\\mathcal O_X$-module sheaves rather than etale coefficient modules, and the coefficient-wise IA hypothesis already states the needed higher-direct-image vanishing.
- Updated `proof_deps`, `citations.json`, and `split_report.tool_uses` to match the repaired Step 3 route.
