## What changed

Proved `AlgebraicGeometry.ProEtale.integralInverseImageComposition_existsUnique`
without changing its statement or the definitions that choose and derive the compositor.
The proof establishes compatibility of the constant coefficient maps on sheafified
constant sections, passes to completed coefficients by the inverse-limit projection
identities, and uses `SheafOfModules.pushforwardComp` and `pushforwardCongr₂`.
Sectionwise extensionality proves uniqueness. Two private continuity instances and
private constant/completed coefficient compatibility lemmas support this proof.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.ProEtale.integralInverseImageComposition_existsUnique`.

The original hole in
`AlgebraicGeometry.ProEtale.integralInverseImageComparison_composition` remains,
with node `lem-trf-integral-inverse-image-comparison-composition` and its unchanged
source and full proof plan. No holes were added and no statements were split off.
The item module compiled without warnings in 4.6 seconds in the final single-file check.

## No longer needed

No existing nodes or imports are pruned by this partial delivery: the remaining
composition theorem still needs its original proof dependencies. The experimental
composition-morphism split and the counit/tower helper modules are not delivered.

## Where the brief, the DAG or earlier work was wrong

The retained report described an obsolete split and incorrectly said that the
compositor proof remained pending. This delivery supersedes that report. The obsolete
unsubmitted split node has been removed from the packet. The tower calculations remain
in scratchpad only; they do not justify claiming the composition theorem proved.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
