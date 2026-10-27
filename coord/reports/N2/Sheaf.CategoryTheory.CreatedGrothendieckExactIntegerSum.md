## What changed

Proved `CategoryTheory.createdGrothendieck_exactIntegerSum` in
`Sheaf.CategoryTheory.CreatedGrothendieckExactIntegerSum`, with its signature and all
imports unchanged. The proof transfers separators by the adjunction hom equivalence and
faithfulness, and transfers AB5 using Mathlib's `HasExactColimitsOfShape.domain_of_functor`.
Mathlib provides the canonical finite-subsum cocone and its natural colimit comparison,
exact coproducts, and invertible kernel/cokernel comparisons. Preservation of finite
colimits by `liftToFinset` is proved pointwise using `liftToFinsetEvaluationIso`.
For the integer sum, `colimitIsoFlipCompColim` identifies the sum with a functor into
families followed by exact coproducts. Exactness transfers through the given natural
isomorphism and is reflected through `U`.

Updated the existing node's proof and proof origin to record this direct Mathlib route.
The proof dependency set is unchanged. No definitions, statement signatures, source-library
files, public imports, or unit routes changed.

## Proved and sorry left

Closed 1 hole: `CategoryTheory.createdGrothendieck_exactIntegerSum`
(node `lem-sf-created-grothendieck-exact-integer-sum`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered Lean module.

Server compilation succeeds without warnings (4.9 seconds). A separate server compile with
`#print axioms CategoryTheory.createdGrothendieck_exactIntegerSum` reports exactly
`propext`, `Classical.choice`, and `Quot.sound` (4.8 seconds).

## No longer needed

None. No import, declared dependency node, or module is pruned. All seven existing proof
dependencies remain used; in particular the joint reflection lemma is used for evaluation
functors to recover pointwise short exactness. The proof needs no additional Sheaf or
WeilConjectures modules and introduces no intermediate statements.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. Mathlib already implements the canonical finite-subsum and
AB5-to-AB4 constructions, so the detailed universal-property arguments can be reused.
The generator argument uses faithfulness of `U` directly. Reflection of finite limits and
colimits gives the final exactness result directly, with no separate comparison-map lemmas.
These implementation choices are reflected in the updated node. The canonical finite sums
cover empty subsets, and the integer coproduct uses Mathlib's universe-shrinking instances.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
