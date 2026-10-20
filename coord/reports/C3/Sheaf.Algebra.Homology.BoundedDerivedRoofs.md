## What changed

Proved `DerivedCategory.boundedDerivedRoofs` in
`Sheaf.Algebra.Homology.BoundedDerivedRoofs`, preserving its complete statement,
universes, visibility and all four conjuncts. Four proved private helpers implement
unbounded common refinement, componentwise homotopy descent along epimorphisms,
the lower-truncation isomorphism above its cutoff, and boundedization of a common
refinement. No public definitions or other modules changed.

The first three conjuncts use Mathlib's `quotientCompQhIso`,
`exists_iso_Q_obj_of_isGE_of_isLE`, and
`right_fac_of_isStrictlyLE_of_isStrictlyGE`. Common refinement uses
`MorphismProperty.RightFraction.map_eq_iff` in the homotopy category.
The final source is `(Z.truncLE b).truncGE (a - 1)`; naturality constructs both
refinement maps. Their quasi-isomorphism follows by two-out-of-three.
Both chain homotopies descend by cancelling the degreewise epimorphism.

Updated the existing node's proof, proof dependencies and proof origin to record
the actual truncation calculation and direct use of Mathlib's API. The unit's
route and the node statement stay intact. The only local lint option preserves
the original named instance binders in the main statement; it affects no proof
or interface.

## Proved and sorry left

Closed 1 of 1 original holes: `DerivedCategory.boundedDerivedRoofs`
(node `lem-kun-bounded-derived-roofs`). Added 0 holes; split off 0.
There are no remaining `sorry` declarations in the delivery.
All four private helper theorems are proved. The final single-file compile
passed without errors or warnings in 3.0 seconds. The delivery preflight checks
the axioms of all delivered declarations independently.

## No longer needed

Removed `import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`.
The proof uses Mathlib's canonical cochain-complex truncations, already available
from the existing imports. It uses no declaration of that composite module,
including `CategoryTheory.IsSequentialHomotopyColimit`, and needs none of its
sheaf-colimit, telescope, stalk, or hypercohomology machinery.
Removed `def-kun-truncations` from this node's proof steps and proof dependencies.
This prunes that module and node from this proof branch; no claim is made that
other target branches cease to use them. All six other original proof dependencies
remain used. No existing public import was removed.

## Where the brief, the DAG or earlier work was wrong

The original proof is mathematically correct. Its `def-kun-truncations` dependency
was represented in Lean by a composite module whose sole new declaration concerns
sequential homotopy colimits; importing it was unnecessary for the canonical
truncation construction. Cutting one degree below the common support makes the
boundary homotopy descent an explicit zero-target argument and avoids constructing
a new map out of the boundary cokernel by hand.

The sandbox contained only dispatcher metadata when this resumed turn started;
there was no interrupted delivery or saved proof packet for this item. Shared-root
logs belonged to another item and were left untouched.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
