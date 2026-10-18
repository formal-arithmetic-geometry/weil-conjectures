## What changed

Proved `AlgebraicGeometry.hProjective_properness` in
`Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper` without changing its signature.
The first conjunct uses the already proved `IsHProjective.isProper`; the remaining
conjuncts use the existing relative-projective-space, closed-immersion/finite, and
composition instances. This retains the factorization argument of the blueprint through
the source library proof. Updated the node proof to record the exact declarations used.

Validation: the single-file server compile passed without warnings; the delivery dry run
passed compilation and the stage-3 preflight. The node update requires independent CODEX review.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.hProjective_properness`
(node `lem-kun-projective-implies-proper`). Holes closed: 1; holes added: 0;
holes remaining in the delivery: 0. No split-offs.

## No longer needed

Removed the proof import `Mathlib.AlgebraicGeometry.ZariskisMainTheorem`:
closed immersions are already proper through the finite-morphism instances imported by
`Mathlib.AlgebraicGeometry.Morphisms.Proper`; the proper-and-mono equivalence is unnecessary.
All five stated proof-dependency nodes remain relevant, including the projective-space
properness tool approval. No Sheaf or WeilConjectures dependency module is withdrawn.
The three public imports remain because they supply the notions in the theorem signature.

## Where the brief, the DAG or earlier work was wrong

The docstring's `IsHProjective.exists_closedImmersion` name is historical: the canonical
source definition supplies `IsHProjective.exists_isClosedImmersion`, with an arbitrary
finite coordinate type. There is no need to convert that type to `ULift (Fin (N + 1))`
for the first conjunct: the source library already proves properness for all finite
coordinate types (including the empty type). The second conjunct still uses exactly the
specified `N + 1` coordinates, with `N = 0` covered by the same finite-type instance.
No statement repair or target change was necessary.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
