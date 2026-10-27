## What changed

Filled the proof of `CategoryTheory.SpectralSequence.spectral_page_zero_propagation` in
`Sheaf.Algebra.Homology.SpectralPageZeroPropagation`. The statement, docstrings and imports
are unchanged. The proof follows the existing DAG plan: apply
`ShortComplex.isZero_homology_of_isZero_X₂` to the page's associated short complex,
transport along the inverse of `E.iso`, and induct with `Int.leInduction` from the
arbitrary starting page. The two page-two hypotheses give off-row support by a sign
case split. The stationary object is zero by its isomorphism with the starting page
of the stationary range.

## Proved and sorry left

Closed the one existing hole in
`CategoryTheory.SpectralSequence.spectral_page_zero_propagation`
(node `lem-weil-pbc-spectral-page-zero-propagation`). Zero holes remain in the item;
zero holes were added, and no statements were split off. The proof uses only Mathlib
and the supplied spectral-sequence structure.

## No longer needed

None. All existing imports are retained and used. Both planned proof dependencies,
`def-sp-spectral-sequence` and `lem-weil-pbc-short-complex-zero-homology`, are used
through their Mathlib declarations. No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancies found. The proof uses Mathlib's associated short complex
`(E.page r hr).sc (p, q)` directly, avoiding explicit neighbour-index arithmetic, and
`Int.leInduction` packages the planned induction on the nonnegative page difference.
These implement the existing plan without changing its dependencies or the unit route.
Boundary cases are covered: the induction base is page r = s; p ≥ 0 and q = 0 makes
no vanishing claim; a stationary range can start at R = 2. Searches with Lean Finder,
Loogle and local ripgrep found the short-complex ingredient but no direct theorem for
arbitrary integer starting pages and integer bidegrees.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
