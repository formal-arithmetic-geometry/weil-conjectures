## What changed

Proved `WeilConjectures.IntegralProjectionReduction.OpenCoordinates.integralOpenAdjunctionReduction`
from the existing unary finite-evaluation statements. Added private categorical lemmas for
pasting unit squares, reflecting equality between reduced constructible objects, and deriving
the counit square from the unit square. The declaration signature and public imports are unchanged.
Updated the item's DAG proof and proof dependencies to this argument.

## Proved and sorry left

Closed the one original hole in `integralOpenAdjunctionReduction`
(node `lem-sf-integral-open-adjunction-reduction`). No holes added; no holes remain in this module.
The unary evaluation statements used by the proof are existing obligations, not new split-offs.

## No longer needed

No existing imports were removed and no module is withdrawn. The planned direct dependency on
`lem-sf-generator-reduction-coherence` (`Sheaf.SixFunctors.GeneratorReductionStatement`) is
unnecessary: the two unary evaluation statements and the datum's finite adjunction normalization
suffice. `lem-sf-open-reconstruction-effectivity` is still used by the coefficient-coordinate
construction; this proof needs no additional reconstruction-effectivity argument. All statement
dependencies and the blueprint unit route are retained.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan described constructing a lifted unit and repeating the quotient
normalization calculation. Existing unary evaluation declarations already isolate those
calculations. This delivery instead pastes their squares, uses fullness together with integral
joint faithfulness to reflect equality, and derives the counit equation by the adjunction
triangle identities. It makes no faithfulness claim for unrestricted derived evaluation.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
