## What changed

Proved both normalization and uniqueness theorems in
`Sheaf.Paper.MixedReductionUnit`. The ordinary transformation is the transpose of the
composite tensor units. The derived transformation is the universal left-derived lift,
using the existing K-flat resolution and change-of-rings preservation results. Added
proved private categorical helpers and proof imports, and recorded this route in
`def-weil-mixed-reduction-unit`.

## Proved and sorry left

Closed two existing holes:
- `WeilConjectures.sfMixedReductionUnit_existsUnique`.
- `WeilConjectures.sfMixedReductionDerivedUnit_existsUnique`.

No holes added or split off. No `sorry` remains in the delivered module. These proofs
use existing library declarations, some of which still carry their own recorded holes.

## No longer needed

None. Both existing public imports supply definitions appearing in the statements or
definitions. No declared dependency or unit step is bypassed, and no module is withdrawn.
The proof uses existing generic tensor adjunctions and K-flat localization, so no new
specialized tensor reassociation theorem is needed.

## Where the brief, the DAG or earlier work was wrong

The node had an empty proof plan. Its updated proof records the ordinary adjunction
construction and the derived resolving-class argument. All existing public statements
and constructions are preserved. There is no mathematical dispute or definition repair.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
