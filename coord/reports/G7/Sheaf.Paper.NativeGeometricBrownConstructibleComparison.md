## What changed

Filled the two proofs in `Sheaf.Paper.NativeGeometricBrownConstructibleComparison`.
Preservation uses the supplied realization image descriptions and compact-support comparison.
The main proof composes and transports the three adjunctions, calculates its counit and
stage-input Hom formula, and constructs the comparison with an arbitrary hull adjunction
as the transpose of that counit. The localizing Hom test proves it is invertible; the
zero-cone criterion gives vanishing. Added only proved private transport helpers. Updated
the item's node proof to describe these calculations. Existing public signatures and
public imports are preserved.

## Proved and sorry left

Closed the two original holes:
- `WeilConjectures.NativeGeometricBrown.preserves_constructible`.
- `WeilConjectures.NativeGeometricBrown.native_geometric_brown_constructible_comparison`.

No holes added, no split-off statements, and no `sorry` left in the delivered module.
The proof uses the supplied stage adjunction and realizations; it does not claim to prove
their separate existence theorems.

## No longer needed

No dependency nodes or modules pruned. The same five mathematical steps remain necessary.
The natural Hom-bijection constructor is implemented by Mathlib's adjunction composition
and transport API, whose underlying construction supplies those same natural bijections.
Removed the redundant private import `Mathlib.CategoryTheory.Triangulated.Pretriangulated`:
its API is already publicly available through the existing triangulated subcategory import.
No new imports are needed, and the existing public imports retain the published interface.

## Where the brief, the DAG or earlier work was wrong

The proof plan's appeal to repleteness has no registered native constructible instance in
the supplied interface. Both occurrences can instead use the stronger supplied image
characterization: compose a realization-image isomorphism with the comparison isomorphism.
This proves exactly the original statement without an interface or definition repair.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
