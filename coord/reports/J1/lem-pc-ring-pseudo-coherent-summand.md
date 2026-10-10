# Stage-1 report: lem-pc-ring-pseudo-coherent-summand

## Files written

- `dag/nodes/sec-picard-framework/lem-pc-ring-pseudo-coherent-summand.json`: split the ring direct-summand proof into the Tag 064X shift and descent argument.
- `dag/nodes/sec-picard-framework/lem-pc-ring-pseudo-coherent-distinguished-triangle.json`: statement-only ring triangle closure lemma; Mathlib no match.
- `dag/nodes/sec-picard-framework/lem-pc-ring-pseudo-coherent-recognize.json`: statement-only high-degree vanishing recognition lemma; Mathlib no match.
- `citations.json`: verbatim node-statement quotes for every cited step dependency.

## Attachments

None. I found no sorry-free project declaration with the item tag or an exact item statement.

## WANTED

None.

## What was wrong and what changed

The item was unsplit despite its source proof depending on two external ring-level facts. I searched the DAG and blueprint and found no existing node stating the ring distinguished-triangle closure or the vanishing recognition lemma, so I created those as statement-only nodes. Tag 064T is a clause of the item itself, so its finite-free construction is written directly in the final item step rather than split into a child node. The original item statement and its Stacks source were preserved.

## Not duplicates

lem-pc-ring-pseudo-coherent-distinguished-triangle vs lem-pc-pseudo-coherent-distinguished-triangle: the new node is the ring-level three-clause m-pseudo-coherence statement in D(R), while the existing node is only the scheme-level two-endpoint pseudo-coherence implication in D(O_Y).

lem-pc-ring-pseudo-coherent-recognize vs lem-pc-pseudo-coherent-bounded-finite-free-model: the new node recognizes m-pseudo-coherence from vanishing cohomology above m, while the existing node changes a pseudo-coherent derived object into a bounded-above finite-free representative under an explicit cohomology bound.

## Review by J1

I read More Algebra Tags 064X (`lemma-summands-pseudo-coherent`), 064W (`lemma-cone-pseudo-coherent`), 064Y (`lemma-recognize-pseudo-coherent`), and 064T (`lemma-pseudo-coherent`) in `more-algebra.tex`, including the exact hypotheses that R is arbitrary, m is any integer, and the distinguished triangle is in D(R). Step 1 uses the source's direct-sum distinguished triangle and the second clause of the new ring triangle node; the finite direct-sum cohomology observation only establishes bounded-above status. Step 2 uses the triangle closure node for the shifted triangles and the recognition node once bounded-above vanishing is reached; the induction and backward descent match the source. Step 3 checks symmetry and writes the 064T finite-free construction directly because that criterion is a clause of this item. Every quote in `citations.json` is copied verbatim from the cited node statement.

I checked the small cases of the item: zero summands, a one-term finite free complex over a field, and a split sum of two bounded-above finite free complexes. The two new statements were tested against these cases and against the source's displayed triangles. Mathlib searches were run for each new node with LeanFinder, Loogle, and grep; only generic derived-category or mapping-cone infrastructure appeared, so no Mathlib leaf was claimed. No duplicate Stacks tag or matching DAG statement was found.

## Unfinished

Nothing.

## Second reading by J1

- Item statement: checked against More Algebra Tags 064X and 064T; arbitrary ring, integer m, direct-summand hypotheses, and bounded-above finite-free consequence agree, including zero and field cases.
- Step 1: checked against the displayed direct-sum triangle in Tag 064X and Tag 064W; corrected the closure clause and made the needed monotonicity from m- to (m+1)-pseudo-coherence explicit.
- Step 2: checked against the shift induction and backward triangles in Tag 064X; expanded shift invariance, the choice of the vanishing shift, and each backward application of the first triangle clause.
- Step 3: checked against the Tag 064T construction; corrected truncation direction, removed the false elementary label, and recorded the descending finite-free construction used for the converse.
- Node `lem-pc-ring-pseudo-coherent-distinguished-triangle`: checked against Tag 064W hypothesis by hypothesis; self-contained statement, definition dependency, source tag, and recorded Mathlib searches pass.
- Node `lem-pc-ring-pseudo-coherent-recognize`: checked against Tag 064Y part (1), including the `i >= m` vanishing boundary; self-contained statement, definition dependency, source tag, and recorded Mathlib searches pass.

Changes made: repaired the wrong triangle-clause citation, stated monotonicity and shift arguments, expanded the descent and Tag 064T finite-free construction, corrected truncation orientation, and synchronized `citations.json` with the revised dependencies.
