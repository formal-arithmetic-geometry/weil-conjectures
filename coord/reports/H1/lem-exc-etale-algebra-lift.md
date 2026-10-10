Files written:

- `dag/nodes/sec-smooth-purity/lem-exc-etale-algebra-lift.json`: statement split; no new nodes; Mathlib searches found no exact quotient-lifting theorem.

Attachments:

- None. No sorry-free project declaration states the item.

WANTED:

- None. The Stacks source for Tag 04D1 is represented by the imported source citation and the blueprint proof; no additional document was needed.

What was wrong or incomplete in the imported item:

- The imported one-paragraph proof conflated three arguments and did not identify which part was elementary. I separated the Jacobian determinant calculation, the reduction isomorphism, and the converse existence assertion.
- The imported node had no blueprint `from` place, no `same_as` result, no Mathlib search log, and status `imported`; these are now filled for a stage-1 split.
- The existing node `lem-exc-etale-jacobian-presentation` is in another unit. It is used as a generic tool because it supplies exactly the characterization required by both directions; this is declared in `split_report.tool_uses`.

## Review by H1

I read the imported item and its source citation to Stacks Tag 04D1, together with the blueprint proof text, and read the full statements of `def-exc-etale-algebra-lift` and `lem-exc-etale-jacobian-presentation`. Step 1 uses the definition's lifted quotient presentation and the Jacobian lemma's exact characterization; the block-triangular determinant calculation shows the determinant is `Delta^2`, and `t Delta = 1` makes it a unit. Step 2 uses only the definition's specified image of `t`; adjoining an inverse is the elementary universal-property argument, with no nilpotence hypothesis. Step 3 uses the converse half of the Jacobian lemma and then the coefficientwise lift construction from the definition. I checked that all hypotheses are preserved: the ideal `I` is arbitrary, the starting algebra is etale and finitely presented over `A/I`, and the constructed algebra is over `A`. Small cases `m = 0` and `I = 0` reduce respectively to adjoining an inverse to `1` and to the original presentation, so the reduction claim has the expected behavior. I searched the DAG for Tag 04D1 and for Jacobian-lift keywords before adding no node; the existing Jacobian node is the only required citation. Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch (unavailable), and their actual results are recorded in the item.

## Second reading by H1

- Item statement: checked against Stacks Algebra, Tag 04D1 (`lemma-lift-etale`), hypothesis by hypothesis; verdict: agrees, including arbitrary ideal and the reduction isomorphism.
- Step 1: checked against Tag 04D1's construction and the statements of `def-exc-etale-algebra-lift` and `lem-exc-etale-jacobian-presentation`; verdict: the block-triangular Jacobian calculation and unit argument supply the claimed etaleness.
- Step 2: checked against the displayed quotient presentation in `def-exc-etale-algebra-lift`; verdict: elementary universal-property argument, with the map sending `t` to the inverse of the reduced determinant.
- Step 3: checked against the converse clause of `lem-exc-etale-jacobian-presentation` and Tag 04D1's final sentence; verdict: every etale finite-presentation algebra obtains the required lifted presentation, with no nilpotence assumption.
- New nodes: none; DAG search found the existing Jacobian presentation node, so no duplicate or auxiliary node is needed.
- Small cases checked: `m = 0`, `I = 0`, a field quotient, and the zero ideal; no statement defect found.

Changes made: removed the stale `uses_not_cited` entry for the conventions bundle, which no proof step uses; made the split report's blueprint places explicit for all three proof paragraphs. No mathematical statement or proof step was otherwise changed.
