# lem-weil-pbc-smooth-over-field-dimension-differentials

Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-smooth-over-field-dimension-differentials.json`: split into four source-backed steps.
- No new nodes.

The statement is Stacks Algebra Tag 00TT, implication (1) => (3), and was kept unchanged. Its proof now follows the source: shrink around the prime to a standard smooth algebra (00TA), compute the Kähler differential rank and the pointwise dimension of that standard smooth algebra (00T7), and transport both calculations through localization (00RT and the reviewed open-subspace dimension lemma). Every cited node says the exact fact used in its step. The existing searches already record that the combined dimension/differentials statement is absent from Mathlib; the individual local-standard-smooth, differential-basis, and localization ingredients are reviewed Mathlib leaves.

No `sorry` is introduced. No imports or nodes become unnecessary. No Lean file was written or built. WANTED: none.

The earlier imported node was not wrong, but it had no proof. The current DAG already contains the two nodes that avoid a circular split: `lem-weil-pbc-standard-smooth-over-field-dimension-at-points` explicitly records that it must feed this 00TT node, while `lem-weil-pbc-smooth-ring-map-locally-standard-smooth` supplies the 00TA reduction.

## Review by E1

I independently checked Tag 00TT and the cited 00TA, 00T7, and 00RT statements. The four steps use the standard-smooth neighbourhood, the differential basis and pointwise dimension formula, localization of differentials, and the open-local-dimension comparison exactly where those statements apply; the localization denominator remains outside the prime. The item keeps its original statement and route, and the proof dependencies are the union of the cited nodes. There are no new nodes, no hidden tag-only fact, no cycle, and no hypothesis added. I accept the split after this A-F review.

I checked all four steps against `algebra.tex`, especially the first paragraph of the proof of Tag 00TT and the proofs of Tags 00TA, 00T7, and 00RT. The first step writes out the only suppressed bookkeeping: a localization of `S_u` at `a/u^m` is a principal localization of `S` at `ua`, which remains outside the prime. I checked the cited DAG statements: 00TA gives the standard smooth neighbourhood, 00T7 gives both the Kähler basis and pointwise dimension, 00RT identifies localized differentials, and the open-subspace node identifies local dimensions. The proof uses the reviewed 00T7 dimension node in the intended direction, so it creates no cycle. No new node, private module, or Lean change is present.
