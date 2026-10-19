## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-square-zero-matrix-lift.json`: existing statement split into four elementary steps; no complete Mathlib match. All inherited search records are retained, and queries run for Q30 are appended from `searches.jsonl`.
- `citations.json`: the single proof-node citation, with the literal matrix-definition sentence used by step 1.
- `report.md`: this report and the direct-delivery self-review.

New nodes: none. New Mathlib leaves: none. Attachments: none. WANTED: none. Unfinished mathematics: none.

The statement, its noncommutative scope, and all three displayed formulas are unchanged. The prior item had no proof. I supplied the omitted finite algebra calculation, rather than introducing a node for one of the item's own clauses. No Lean was written, no compiler was run, and no project or launcher files were edited.

## Source and route

I read `dag/chapters/sec-six-functors-basics.json`, `dag/units/sk-lem-coefficient-heart.json`, the current main-20261015 text of `det-lem-coefficient-heart-closure`, and the parent's reduction-equivalence statement and matrix-lifting proof step (step 6). This item supplies exactly the correction of a matrix inverse modulo the square-zero kernel used there; it does not replace the unit's monodromy route. The item's blueprint ancestry remains `det-lem-coefficient-heart-closure` through the two existing intermediate nodes. Its `from.place` now names current clause (2) and the parent's exact step, rather than implying that the current ancestor Markdown contains a second proof paragraph. This is not a unit or chapter change.

I read Bhatt--Scholze, *The pro-etale topology for schemes*, Proposition 6.8.4(1), printed p.59, in the supplied PDF. The proposition identifies integral lisse sheaves with their compatible reductions, and the source omits proof (1). I therefore marked the proof as agent-written and identified it as the explicit omitted calculation, not as text present in the paper. The more general arbitrary-ring algebra statement is valid without commutativity, and is already the seeded statement of this item. It supplies the commutative coefficient-ring application of its parent. No SGA source is used.

## Searches and reuse

For the attachment check I searched all `WeilConjectures/` in `/home/ubuntu/weil-src-slopmaster2` for the exact item id, square-zero/nilpotent matrices, and matrix-lifting terminology. There is no declaration stating the item. The id search and concept search returned unrelated square-zero extensions, idempotents, and geometric thickenings; none provides these inverse formulas for an arbitrary quotient. The read-only upstream master is not being treated as proof evidence.

I searched the whole DAG by square-zero, nilpotent/matrix, and lifting/inverse terms, and used `tools/blueprint_refs.py search` with `square-zero` and `inverse matrix` as well as a combined preliminary query. The square-zero blueprint hit is the disjointness-thickening setup, not a matrix inverse assertion. There is no second blueprint statement of this item, so `same_as` remains empty. `blueprint_refs.py ancestor` returned `det-lem-coefficient-heart-closure`. There are no new-node duplicate pairs to justify.

The actual Q30 Mathlib calls are logged in `searches.jsonl`; I read the returned signatures and also read `Mathlib/RingTheory/Ideal/Quotient/Nilpotent.lean:53` and the inverse-uniqueness declarations at `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:480`. Both semantic phrasings were tried. `IsNilpotent.isUnit_quotient_mk_iff` requires `CommRing` and states no prescribed inverse formula. The `TrivSqZeroExt` hits concern a split extension, not a general square-zero quotient (for example Z/4 -> Z/2 need not split). `Matrix.right_inv_eq_left_inv` assumes the two identities that must be proved here. Woodbury-type invertibility hits assume invertibility data unrelated to reduction modulo this ideal. These do not make the full item a one-line Mathlib specialization. No service failure was recorded as a negative result.

## Review by Q30

I checked B--E of `coord/delivery-errors.md` against the item, the literal statement of its only cited node, and the PDF source. There are no new statements to audit under B1--B9: the existing statement is self-contained, defines its two-sided square-zero ideal and quotient, and uses the existing matrix definition. The exact hypotheses are a unital ring, a two-sided ideal annihilating all pairwise products, a finite square size allowing zero, and an inverse after reduction. No commutativity, nontriviality, local-ring, determinant, or splitting hypothesis is introduced.

Step 1 cites only `def-weil-matrix`. I opened that node: it defines matrices as families of entries over an arbitrary ring, which is exactly what this step takes from it; it does not claim to define multiplication. Multiplication and identity are explicitly given by their entry formulas in the step. The quotient's coset definition gives representatives and says exactly that zero coset means membership in I. Preservation of the finite multiplication sums is expanded from quotient operations, so no non-elementary quotient-matrix comparison is hidden. Finite entry choices also include the empty index set. The quote in `citations.json` is the actual matrix-family sentence, not a theorem falsely attributed to that definition.

Step 2 uses only the entries in I established in step 1 and the pairwise-product-zero hypothesis. It explicitly sums the zero products to prove N squared and P squared vanish. To avoid treating the matrix-ring laws as an uncited theorem, it spells out the two finite double sums giving associativity, distributivity by expanding sums, and the Kronecker-delta identity. Reordering finite sums uses only additive commutativity of a ring, not scalar multiplicative commutativity. This is a routine entry calculation, not a separate non-elementary matrix-ideal lemma.

Step 3 uses the preceding zero squares and the definitions N=BC-1 and P=CB-1. The two displayed expansions prove respectively the right and left inverse equations in the required order. No commutation of B, C, N or P is used. There is no appeal to a theorem about one-sided inverses over noncommutative rings.

Step 4 proves equality of the corrections by expanding both as C-(CBC-C). Thus it uses no inverse-uniqueness lemma and supplies the third clause, rather than assuming it. Combined with step 3 the common matrix has both inverse properties. All four steps are marked elementary because they contain these actual finite ring calculations. Their texts are each below 800 characters; there is no long step concealing an independent comparison lemma.

Small-case checks: if r=0, the matrix type has one element, identity equals zero, the choice is empty and all equations hold. If I=0, C is already an inverse and both corrections equal C. For R=Z/4, I=(2), r=1, B=3 and C=1, one has N=P=2 and both corrections equal 3. To check order in a noncommutative ring, take R the upper-triangular 2-by-2 matrices over F_3, I its strictly upper-triangular ideal, r=1, B=((1,1),(0,2)) and C=((1,0),(0,2)). Then N=2e_12, P=e_12, and both corrected inverses are ((1,1),(0,2)); multiplying on either side gives identity. This example has N different from P, so equality was not obtained by conflating them. The zero ring and the possible I=R case also satisfy the formulas; I=R square-zero forces the zero ring by 1 times 1=0.

No C4 mismatch remains: the sole citation supplies only families of entries and its exact quotation is recorded. No C1 fact remains hidden: all quotient, finite sum, nilpotence and inverse arguments are written out. There is no cycle, no off-unit statement dependency, no new node restating a clause (D1/D2), and no silent statement correction. The only repairs to the seeded item were adding the proof, completing the precise blueprint place and recording this attempt's searches.
