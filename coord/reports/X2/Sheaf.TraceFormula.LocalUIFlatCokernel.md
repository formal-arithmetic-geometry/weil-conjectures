## What changed

Proved `Module.flat_of_universally_exact` in
`Sheaf.TraceFormula.LocalUIFlatCokernel`, preserving its complete signature,
visibility, public import, and docstrings. The proof applies Mathlib's flatness
criterion in the given testing universe and performs the tensor diagram chase
using the quotient of an arbitrary injection. Updated the existing node's proof
and proof origin to match the Lean argument. No other modules changed.

Searches through msearch (LeanFinder, Loogle, and grep) and direct searches of
Mathlib, WeilConjectures and Sheaf found the flatness criterion and tensor right
exactness API, but no direct theorem for this cokernel statement. The proof uses
only the existing public import `Mathlib.RingTheory.Flat.Basic`.

## Proved and sorry left

Closed 1 hole: `Module.flat_of_universally_exact`
(node `lem-trf-local-ui-flat-cokernel`). Added 0 holes; 0 remain in the item.
No lemmas were split off. Server compilation and an explicit `#print axioms`
check verify the completed proof with exactly `propext`, `Classical.choice`,
and `Quot.sound`; delivery performs the required checks again.

## No longer needed

No imports, nodes, or modules removed. The only stated dependency,
`def-weil-pbc-flat-ring-map`, remains used through Mathlib's flatness criterion.
The original plan's intermediate demonstration that M₁ is flat is unnecessary:
right exactness already gives the left-column exactness needed in the cokernel
chase. No separate dependency module was assigned to that intermediate step.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or unusable dependency was found. The proof simplifies
the plan as described above. Testing universes are retained exactly: the
criterion's universe is explicitly `max u t`, so the ring fits and the quotient
stays in the same testing universe. No finite generation, nontriviality, or
nonzero-module assumption was added, including for the zero ring and modules.
The unit record has no realized statement or proof-step attachment for this
supporting node, and its route is preserved.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
