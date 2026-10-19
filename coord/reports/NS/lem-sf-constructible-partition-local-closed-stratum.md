1. Files written:
- `dag/nodes/sec-smooth-purity/lem-sf-constructible-partition-local-closed-stratum.json` — statement, split proof, no new nodes.
- `citations.json` — verbatim dependency quotations.

2. Attachments: none.

3. WANTED: none.

4. The imported node was unsplit and had only two old Mathlib grep searches. I retained its statement and added the three-step Stacks argument. Existing nodes cover all non-elementary ingredients: locally closed subsets, constructible restriction to an open, and constructible implies retrocompact. No child node was justified. Mathlib searches were rerun with leanfinder, loogle, grep, and leansearch (leansearch unavailable); the existing open-restriction and retrocompact nodes were used.

5. Nothing remains unfinished.

## Review by NS
I checked the parent source route in `lem-sf-proetale-constructible-origin`, whose Step 5 needs an affine neighbourhood where the chosen stratum is closed and the complement quasi-compact. I read the statements of every cited node. Step 1 uses the locally closed definition to write the chosen stratum as an open intersected with a closed set, then shrinks to an affine open. Step 2 uses the same definition for local closedness after restriction and the cited open-restriction lemma for constructibility; its hypotheses are the open immersion of the affine neighbourhood and the original constructibility of each stratum. Step 3 uses the Boolean-complement clause in the constructible-subset definition and the cited constructible-is-retrocompact statement with the affine open itself as the quasi-compact test open. I verified that every citation quote is verbatim in `citations.json`, that all proof dependencies exist, and that no new node duplicates an existing statement.


## Second reading by NS

- Item statement: checked every hypothesis and clause against Topology 005J (lemma-open-immersion-constructible-inverse-image), 005H (lemma-constructible), 09YH (lemma-constructible-is-retrocompact), Schemes 01IT (lemma-basis-affine-opens), Algebra 00E8 (lemma-quasi-compact), and Pro-etale Cohomology 09AK (lemma-compare-constructible), proof's local closed-stratum reduction; PASS. No Noetherian or quasi-separated hypothesis on $Y$ is needed. The finite partition identifies $k$; no further stratification condition is used. For the empty scheme or $N=0$ there is no $y$, so the assertion is vacuous. For $N=1$, $Y_k=Y$ and the complement is empty. Over a field it is the one-point assertion. Empty other strata stay empty and constructible; the zero ring gives the empty case.
- Step 1: checked def-weil-locally-closed-subset and lem-weil-pbc-affine-opens-basis against Topology Basic notions 004E and Schemes 01IT; PASS after adding the existing affine-basis leaf. $y\in Y_k$ implies $y\in W$, so the basis lemma applies. $Z\cap V$ is closed by the subspace topology; no claim that intersections of affine opens are affine is made.
- Step 2: checked both cited statements against Topology 005J; PASS after writing $Y_\nu\cap V=(W_\nu\cap V)\cap(Z_\nu\cap V)$. Restriction uses only that $V$ is open and $Y_\nu$ constructible; neither quasi-compactness of the inclusion nor a locally closed image factorization is assumed.
- Step 3: checked def-weil-constructible-subset's Boolean clause against 005H, lem-weil-pbc-affine-scheme-qcqs's quasi-compact clause against Algebra 00E8, and lem-weil-pbc-constructible-is-retrocompact against Topology 09YH; PASS after adding the existing affine-qcqs leaf. The space in the retrocompact lemma is $V$, and its quasi-compact open test subset is all of $V$. The openness conclusion follows from Step 1. The argument does not use a cited node's proof or any hidden spectral-topology assertion.
- New nodes: none; PASS B1–B7 and D1–D2 vacuously. Existing-node searches for 00E8/090M and affine-basis keywords found the two exact ingredients; their statements and Mathlib source were opened (AffineScheme.lean:305 and :561). Open restriction source at Topology/Constructible.lean:254 agrees with 005J. All added dependencies are existing Mathlib leaves; the retained non-leaf retrocompactness lemma is a generic tool from the proper-base-change unit, whose statement is exactly needed and has no special scheme hypotheses. No tool_uses field was written.

Changes and reasons:
- Added lem-weil-pbc-affine-opens-basis to Step 1 and lem-weil-pbc-affine-scheme-qcqs to Step 3, repairing C1. Step 1 is no longer marked elementary because it invokes the affine-basis theorem.
- Expanded Step 2's locally closed restriction into its two factors, eliminating a hidden “remains” argument (E5).
- Replaced the unused spectral-topology source route (0901/090M) with the actual 09YH/00E8 route and supplied precise labels at each step; the statement is unchanged.
- Regenerated citations.json with verbatim full statements of every cited node, including both added citations.
- Ran independent msearch queries: loogle `Topology.IsConstructible, IsRetrocompact` returned six ingredient declarations, not this neighbourhood theorem; grep `isCompact_univ|isBasis_affine|isTopologicalBasis.*affine|IsConstructible.preimage` in AlgebraicGeometry returned the affine-basis usages; leanfinder with a scheme-neighbourhood/compactness formulation returned eight related declarations, none stating the item's three clauses. Actual outputs are in searches.jsonl. Earlier Loogle syntax/unknown-identifier errors are errors, not evidence of absence; no new search claim relies on them. No new Mathlib leaf or Lean declaration attachment was justified.

Validation: deliver.py NS lem-sf-constructible-partition-local-closed-stratum --no-push printed OK at b798a8e5fb; preflight passed. Only stage-1 JSON/report changes were made; no compiler, Lake or build tools were run.
