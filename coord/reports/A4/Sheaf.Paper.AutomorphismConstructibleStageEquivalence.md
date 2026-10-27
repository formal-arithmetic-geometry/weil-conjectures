## What changed

Filled the integral and rational square existence-and-uniqueness proofs, finite
commuting-square coherence, the scalar
square compatibility, and common-stage coefficient linearity in
`Sheaf.Paper.AutomorphismConstructibleStageEquivalence` without changing their signatures.
The integral comparison is a natural isomorphism built from the specified realization,
whole-system counit, and compositor. The rational comparison extends its components
through scalar localization, with naturality proved by tensor induction.
Added proved private helpers for these constructions. Finite coherence uses the ordinary
module-square identity and pasting equations, their derived images, and cancellation
of the derived compositors. Added private proof imports of
`Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange` (including its private coherence
helpers) and `WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor`.
No signature or public import changed.

The cached finite-stage linearity instance explicitly uses the same canonical
scalar-localization and integral linear instances to avoid expensive inference; see
`coord/changes/A4-stage-linear-elaboration.md`. Its only textual user is this item;
the downstream public interface needs no adaptation. Local transparency settings
prevent expansion of the derived-category construction during instance inference.
The four-proof version compiled in 42.8 seconds. The combined five-proof version
compiled in 41.1 seconds. A local irreducibility setting for residue fields avoids
repeated expansions while matching invertibility instances. The node copy records the five implemented clauses.

## Proved and sorry left

Closed five of the twelve original holes:

- `automorphismStageIntegralSquare_existsUnique`.
- `automorphismStageRationalSquare_existsUnique`.
- `automorphismConstructibleStage_finite_coherence`.
- `automorphismConstructibleStage_square_scalar`.
- `automorphismConstructibleStage_qbar_linear`.

Added zero holes. The following existing holes remain, all attached to
`lem-sf-automorphism-constructible-stage-equivalence`:

- `automorphismStageQbarSquare_existsUnique`.
- `automorphismConstructibleStage_comparison_system`.
- `automorphismConstructibleStage_square_reduction`.
- `automorphismConstructibleStage_integral_coherence`.
- `automorphismConstructibleStage_integral_shifts`.
- `automorphismConstructibleStage_descended_shifts`.
- `automorphismConstructibleStage_inverse_comparisons`.

## No longer needed

None. The unfinished parts retain their declared dependencies; no module or node is withdrawn.
No public or proof imports were removed.

## Where the brief, the DAG or earlier work was wrong

No statement correction. This is a partial delivery on a module with several holes.
The new proofs implement the stated integral construction and rationalization steps.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
