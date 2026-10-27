## What changed

Proved `CategoryTheory.SheafDifferentials.inverseDifferentials_identity`.
The proof constructs the underlying additive and scalar transport map from the recorded
`moduleAdd` and `moduleSMul` equations, lifts it to a module morphism, and uses the
sheafification universal property to show that its composite with the normalized
comparison is the identity. The existing imports and definitions were retained.

## Proved and sorry left

Closed the hole in `inverseDifferentials_identity`.

The following three theorem holes remain, each in the item's original module and node:

- `CategoryTheory.SheafDifferentials.inverseDifferentials_existsUnique`
- `CategoryTheory.SheafDifferentials.inverseDifferentials_naturality`
- `CategoryTheory.SheafDifferentials.inverseDifferentials_composition`

No new `sorry` declarations were added.

## No longer needed

No imports or DAG dependencies were removed. A temporary generalized transport helper
was discarded because the retained identity proof does not use it.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan is mathematically appropriate. The naturality and composition steps
remain separate universal-property arguments and were not silently replaced by weaker
claims. The initial generalized helper exceeded the single-file elaboration limit, so it
was pruned from this delivery; this does not affect the proved identity theorem.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
