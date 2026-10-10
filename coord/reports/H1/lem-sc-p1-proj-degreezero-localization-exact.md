Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-proj-degreezero-localization-exact.json`: split; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-p1-localization-short-exact.json`: new Mathlib leaf; `IsLocalizedModule.map_exact`.
- `dag/nodes/sec-picard-framework/lem-sc-p1-graded-degree-component-exact.json`: new statement-only node; no Mathlib match.
- `citations.json`: verbatim statement excerpts for both cited nodes.

Attachments: none.

WANTED: none. The source used is the repository's Stacks Project copy, `literature/stacks-project/algebra.tex` (Section 00JL and Lemma 00HT) and `literature/stacks-project/constructions.tex` (Lemma 01M7).

The imported item was unsplit and had no exact declaration in the read-only Lean checkout. I searched the DAG, blueprint index, and `WeilConjectures` sources for the item tag and for degree-zero homogeneous localization. The existing restriction-map node `lem-weil-pbc-graded-module-away-restriction` does not state exactness, so it is not a substitute. I added only the two strictly smaller facts used by the proof. The ordinary localization fact is a Mathlib leaf via `IsLocalizedModule.map_exact`; the degree-component fact has no matching Mathlib theorem and therefore carries a statement only.

## Review by H1

I read the item source context in the blueprint proof of `lem-sc-p1-graded-resolution`, then checked the local calculation against Stacks Algebra Section 00JL and Constructions Lemma 01M7 (5). Step 1 cites the ordinary-localization node, whose statement explicitly supplies exactness of `0 -> T^{-1}A -> T^{-1}B -> T^{-1}C -> 0` for a multiplicative subset and an exact module sequence; this is exactly the operation taken in the step. Step 2 is an explicit fraction calculation: homogeneous denominators give the grading `deg(y/h)=deg(y)-deg(h)`, and degree-preserving maps remain graded. Step 3 cites the degree-component node, whose statement explicitly says every homogeneous component of an exact graded module sequence is exact; its degree-zero component is exactly the fraction definition of each `M_(p)`, and the induced map is `y/h -> phi(y)/h`.

For the new localization node I read Mathlib `Mathlib/Algebra/Module/LocalizedModule/Exact.lean`: `IsLocalizedModule.map_exact` states exactness after localization, and the standard localization maps specialize to the node in one line. For the graded-component node I searched LeanSearch, LeanFinder, and Mathlib source grep; no matching declaration was found, so it remains statement-only. I searched existing DAG nodes and blueprint references before creating both nodes and found no duplicate statement. I tested the item on the zero sequence and on the identity short exact sequence; for `S=k[x_0,x_1]`, the primes `(0)` and `(x_0)` satisfy the stated denominator and degree conditions, and the degree-zero identification is unchanged. No hypotheses were added or dropped.

What remains unfinished: the new statement-only graded-component node is queued for a later split, as required by stage 1.
