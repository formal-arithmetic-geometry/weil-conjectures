# Stage-1 report: lem-sc-etale-local-dimension

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-etale-local-dimension.json`: item, split with two proof steps and no new nodes.
- `citations.json`: verbatim statement quotes for every cited node in each step.

## Attachments

None.

## WANTED

None.

## Review by C1

I read the item source, Stacks Project More on Algebra, Lemma 44.2 (Tag 07QP), including both proof paragraphs. The statement agrees with the source: an etale ring map $A\to B$ and a prime $q$ over $p$ give equality of the Krull dimensions of $A_p$ and $B_q$. I also checked the imported blueprint ancestor `lem-sc-brauer-zero` and its recorded place, and searched the DAG and blueprint for duplicate dimension-invariance statements; no node states Tag 07QP itself.

Step 1 follows the source's lower inequality. The existing etale-flat node says an etale affine ring map gives a flat module. The existing flat-local-ring-maps node says that a flat ring map induces the displayed flat local map on localizations, and the existing local-flat-faithfully-flat node says every flat local map of local rings is faithfully flat. The existing faithfully-flat-local-dimension node then states exactly the required inequality. I checked each cited statement verbatim and verified that the contraction of $q$ is the stated $p$.

Step 2 follows the source's reverse inequality through quasi-finiteness. The existing etale-quasi-finite node supplies finite type and quasi-finiteness at every prime; the existing quasi-finite local-dimension node applies to $q$ and its contraction $p$ and gives the reverse inequality. Its hypotheses match the map and primes in the item. Combining the inequalities is elementary.

I tested the statement on the identity map $A=B$ with $p=q$, and on a finite separable field extension (both local rings are fields of dimension zero). The item had no exact sorry-free declaration in the slopmaster2 source. Mathlib searches for the item and both possible auxiliary formulations were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable, while the other searches found only general etale, localization, or quasi-finite infrastructure and no exact theorem for the item. No new node was needed because all non-elementary inputs already exist in the DAG.

## What was wrong or changed

The imported item had an empty proof. I filled the two source-aligned inequalities, retained the statement and dependencies, and marked the item split. No source or blueprint error was found.

## What remains

Nothing for this split.

## Second reading by C1

- Item statement: checked against More on Algebra, Lemma 44.2, Tag 07QP; the etale map, prime contraction, and equality of the two localized Krull dimensions agree hypothesis by hypothesis.
- Step 1: checked against the first proof paragraph of Tag 07QP and the statements of `lem-weil-pbc-etale-algebra-flat`, `lem-weil-pbc-flat-local-ring-maps`, `lem-pc-local-flat-faithful-flat-reflects-surjective`, and `lem-sc-faithfully-flat-local-dimension`; the cited nodes supply flatness, the localized flat local map, faithful flatness, and the lower inequality.
- Step 2: checked against the second proof paragraph of Tag 07QP and the statements of `lem-weil-pbc-etale-ring-map-quasi-finite` and `lem-weil-pbc-dimension-inequality-quasi-finite`; finite type, quasi-finiteness at the chosen prime, and the reverse inequality are all stated by the cited nodes.
- Elementary content: combining the two inequalities is immediate; no other uncited non-elementary fact is used.
- New nodes: none; therefore B1-B7 and duplicate/Mathlib-node checks are vacuous. I searched the DAG for the Tag 07QP result and found only this item.
- Edge cases: identity maps and finite separable field extensions give dimension zero on both sides; the prime contraction hypotheses behave as stated.

No changes were needed after the first reading. The delivery preflight passes, including citations, blueprint metadata, and split ownership.
