# Stage-1 report: lem-pc-perfect-summand

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-perfect-summand.json`: repaired item proof and dependencies.
- `dag/nodes/sec-picard-framework/lem-pc-pseudo-coherent-summand.json`: new statement-only 08CE node; no Mathlib match.
- `citations.json`: verbatim citations for every dependency used by every proof step.

## Attachments

None. No sorry-free project declaration states this item.

## WANTED

None.

## What was wrong and what changed

The returned Step 2 claimed that an idempotent in the derived category can be represented by a chain idempotent that splits degreewise. This is not valid: a derived-category idempotent is only a homotopy-class idempotent, and idempotent completeness of the bounded projective homotopy category is a separate theorem. Step 1 also lacked the required passage from a sheaf-derived object to a bounded projective affine model.

I replaced those steps with the proof route in Stacks Tag 08CS. The existing node `lem-pc-perfect-pseudo-coherent-locally-finite-tor` supplies Tag 08CQ (perfect implies pseudo-coherent and locally finite Tor dimension). The new node `lem-pc-pseudo-coherent-summand` records Tag 08CE (pseudo-coherence is preserved by direct summands). Tag 08CK gives inheritance of the local Tor-amplitude interval by each summand; this is an elementary direct-sum tensor argument. Finally `lem-pc-pseudo-coherent-finite-tor-perfect` gives local perfectness, and `def-pc-perfect-complex` gives locality.

## Review by C1

I read the item and Tag 08CS in `literature/stacks-project/cohomology.tex`, and read the full statements of all cited DAG nodes. Step 1 uses exactly the existing 08CQ-forward node, including its local interval and pseudo-coherence conclusions. Step 2 uses exactly the new 08CE statement, with the same direct-sum hypotheses and both summand conclusions. Step 3 verifies the hypotheses of Tag 08CK on each open from Step 1: tensor distributes over the direct sum, so vanishing outside `[a,b]` passes to both summands; no separate node is needed for this two-line consequence. Step 4 uses the exact hypothesis and conclusion of `lem-pc-pseudo-coherent-finite-tor-perfect` and the local-cover clause of `def-pc-perfect-complex`.

I searched the DAG and blueprint for 08CQ, 08CE, 08CK, and pseudo-coherent summand variants. The 08CQ forward implication already existed; no 08CE node existed, so I created one. I ran LeanFinder, Loogle, and Mathlib grep searches for the new node and found no Mathlib theorem. I checked zero and one-term direct-sum cases and removed the invalid chain-idempotent claim. The item’s statement and source remain unchanged.

## Unfinished

Nothing.

## Second reading by C1

- Item statement: checked against Cohomology of Sheaves, Tag 08CS (`lemma-summands-perfect`); hypotheses and both summand conclusions agree, including zero and one-summand cases.
- Step 1: checked against Tag 08CQ and the full statement of `lem-pc-perfect-pseudo-coherent-locally-finite-tor`; the cited node supplies pseudo-coherence and the local Tor interval.
- Step 2: checked against Tag 08CE (`lemma-summands-pseudo-coherent`) and the new node; the direct-sum hypotheses and both conclusions agree.
- Step 3: checked against Tag 08CK (`lemma-summands-tor-amplitude`); tensor additivity gives the two summand vanishings in a few lines, so this is elementary and needs no dependency node.
- Step 4: checked against Tag 08CQ and `def-pc-perfect-complex`; local pseudo-coherence plus the inherited finite Tor interval gives local perfectness, and locality gives the global conclusion.
- New node `lem-pc-pseudo-coherent-summand`: checked against Tag 08CE, with all notions defined and no Mathlib match in the recorded searches; tested on zero and one-term direct sums.
- Change: removed the incorrect Step 3 dependency on `lem-pc-perfect-pseudo-coherent-locally-finite-tor`, because that node does not state the direct-summand Tor-amplitude result; the step now records the elementary Tag 08CK argument directly.
