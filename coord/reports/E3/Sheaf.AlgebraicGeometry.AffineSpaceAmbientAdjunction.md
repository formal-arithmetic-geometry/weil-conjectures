## What changed

Added the compactification-specific core theorem
`affineSpaceAmbientAdjunction_of_compactification` as an explicit lower-level statement.
The item theorem transports its adjunction to the project-wide compactification-independent
`rightDerivedLowerShriek` using `rightDerivedLowerShriekIso`.

## Proved and sorry left

Closed `nonempty_affineSpaceAmbientAdjunction` (the item theorem). One strictly simpler
geometric sub-result remains as `affineSpaceAmbientAdjunction_of_compactification`.

## No longer needed

None. The existing imports remain because the item signature and compactification transport
use the ordinary derived lower-shriek, finite Tate twist, and compactification APIs.

## Where the brief, the DAG or earlier work was wrong

The supplied module had a single large proof plan but no Lean-level compactification-specific
interface. The proof was reduced by exposing that interface and using the existing unbounded
compactification-independence isomorphism.

## New nodes

Added `cor-amb-affine-space-adjunction-compactification-core` for
`affineSpaceAmbientAdjunction_of_compactification`.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
