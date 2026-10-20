## What changed

Closed the two wrapper proofs in `Sheaf.Paper.PuritySectionInvariantIntrinsic`:
`sectionCompactifiable` uses `comparedCompactification`, and
`sectionInvariantFinite_invertible` installs that compactification and applies the
intrinsic invertibility theorem. The existing intrinsic invertibility theorem remains
open. No public interface imports were added.

## Proved and sorry left

Proved:
- `WeilConjectures.PurityFiniteSetting.sectionCompactifiable`.
- `WeilConjectures.PurityFiniteSetting.sectionInvariantFinite_invertible`.

Sorry left:
- `WeilConjectures.PurityFiniteSetting.sectionInvariantIntrinsic_invertible` (node `def-pur-section-invariant`).

No new holes were added.

## No longer needed

The attempted separate coefficient-realization comparison was withdrawn because it was
not needed for the delivered wrapper proofs. Its temporary module and import were removed.
No existing proof dependency was pruned from the retained declarations.

## Where the brief, the DAG or earlier work was wrong

The wrapper proofs did not require a new tensor-realization theorem: the existing
`sectionInvariantIntrinsic_invertible` interface already supplies the exact result used by
the finite wrapper. The remaining intrinsic proof still needs the coefficient tensor
comparison.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
