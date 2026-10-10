1. Files written

- `dag/nodes/sec-curve-estimates/lem-sc-leray-closed-pushforward-cohomology.json`: statement item, split.
- `dag/nodes/sec-curve-estimates/lem-sc-topological-leray-spectral-sequence.json`: statement-only child, Mathlib no match.

2. Attachments

None.

3. WANTED

None.

4. Problems found

The imported item was unsplit and had been created in the metadata of the earlier closed-immersion item. Its source and statement agree with Stacks Cohomology Lemma 01F4, whose proof invokes the Leray spectral sequence of Lemma 01F2. The returned split had the edge map backwards and incorrectly applied the generic exact-couple collapse lemma by transposing bidegrees. I replaced the child by an explicit first-quadrant spectral-sequence statement with its differentials, page quotients, finite convergence filtration, functoriality, and correctly directed edge map, then made the item's second step the direct row-vanishing argument from that statement. No statement was weakened.

5. What could not be finished

No unfinished work remains.

## Review by C1

I read the item's source in `literature/stacks-project/cohomology.tex`, Lemmas 01F2 and 01F4, and checked the unchanged item statement: a continuous map of spaces, an abelian sheaf, vanishing of every higher direct image, and the natural Leray edge isomorphism in every degree. I searched the whole DAG and blueprint for the Leray statement and for the source labels; no existing node stated this topological spectral sequence. I also searched the Lean source trees for the item tag, Leray labels, and the key terms; no exact declaration was present.

The new child is self-contained: it introduces the continuous map, abelian sheaf, direct image, right derived functors, page terms and differentials, convergence filtration, functoriality, and the edge map, and cites the existing definition nodes for those notions, including `def-sp-filtration`. Its statement is the exact content needed from Stacks Lemma 01F2 and is statement-only because it is not a Mathlib result. I recorded LeanSearch, LeanFinder, and Mathlib-source grep searches, all with no match. Item step 1 uses the child's page, filtration, and correctly directed edge-map clauses. Item step 2 uses only the child: the hypothesis kills every E2 term with b!=0; the bidegree formula shows every differential has source or target off row zero, so all pages stabilize, and the filtration has only the a=n graded piece. I checked that the resulting edge E2^{n,0}->H^n is an isomorphism, including n=0. The former `lem-sp-edge-collapse` citation and tool use were removed because its exact-couple and column-vanishing hypotheses are not supplied by the child.

I checked edge cases p=0 (the edge is the identity on global sections) and f the identity map (higher direct images vanish and the comparison is tautological). No additional hypotheses are used.
