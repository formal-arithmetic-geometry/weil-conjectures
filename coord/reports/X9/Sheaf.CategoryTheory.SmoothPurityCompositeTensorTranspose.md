## What changed

Replaced the hole in `CategoryTheory.spCompositeTensorTranspose_eq` by a complete
counit-transpose calculation following the existing eight-step DAG plan. Private
proved helpers establish inverse-projection naturality and associativity, unit and
coefficient naturality of the tensor mate, the tensor expansion using braiding
coherence, and the direct and iterated composite transposes. Their equality follows
from injectivity of the composite Hom equivalence.

Added a private proof import of `Mathlib.CategoryTheory.Monoidal.CoherenceLemmas`
for equality of the unitors at the tensor unit. Existing public imports, all six
public definitions, and the complete main theorem statement are unchanged.

## Proved and sorry left

Closes the sole original hole:
`CategoryTheory.spCompositeTensorTranspose_eq`
(node `lem-sp-composite-tensor-transpose`). Adds zero holes and splits off none.
No `sorry` remains in the delivered module.

The complete proof compiled successfully in 5.3 seconds. The final delivery
preflight checks the cleaned file and the axioms of every declaration.

## No longer needed

None. No existing import or DAG dependency is removed. All stated proof
dependencies are Mathlib leaves, and the proof uses their recorded adjunction and
monoidal APIs directly. The existing unit route is preserved. The associativity
assumptions for the g and h projections are unnecessary for this calculation but
are retained verbatim in the existing main theorem signature.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The theorem is proved for arbitrary
specified natural projection isomorphisms satisfying its assumptions. Only the
specified coefficient mate is inverted. The proof does not assume invertibility
of any other coefficient mate and introduces no new data construction.

## Second reading by X9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
