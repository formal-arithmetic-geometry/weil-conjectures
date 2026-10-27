## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.exists_finite_hausdorff_affine_cover`.
The finite affine-cover criterion supplies a finite set, enumerated by `Fin n`.
Each ring is the actual coordinate ring `Γ(X, U i)`, with the canonical affine
spectrum isomorphism. The subspace T1 instance transports to the spectrum;
Mathlib's closed-singleton/maximal-prime criterion proves all primes maximal.
The already proved `AlgebraicGeometry.Spec.profinite_of_isMaximal` supplies compactness
and Hausdorffness, transported back to the charts. Existing signatures and imports
are unchanged.

Validation: `lcompile.py` compiled the final module cleanly in 3.4 seconds,
with no warnings. The proof remains the node's four-step argument, using the
existing Mathlib packaging for the maximal-prime step, so no node edit is needed.

Searches: LeanFinder for a finite compact Hausdorff affine cover found the finite
affine-cover criterion and affine compactness, but no theorem with the whole conclusion.
Loogle found `PrimeSpectrum.isClosed_singleton_iff_isMaximal`. The grep search confirmed
that criterion and the finite-cover criterion; source and Sheaf searches found the
existing proved profiniteness theorem and examples of transporting its instances.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.exists_finite_hausdorff_affine_cover`
(node `lem-sfb-t1-finite-hausdorff-affine-cover`). Added zero holes; zero holes remain
in the item. No statements were split off.

## No longer needed

None. No imports removed, no modules withdrawn, and all five planned dependencies
remain used, directly or through Mathlib's closed-singleton/maximal-prime criterion.
That criterion already implements the closure/maximal-ideal argument of step 3.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing Mathlib criterion packages step 3, avoiding
its repetition. The unit route is unchanged. The construction covers empty schemes
and the zero coordinate ring without an extra nonemptiness assumption.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
