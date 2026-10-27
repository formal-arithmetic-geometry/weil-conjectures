## What changed

Proved `AlgebraicGeometry.ProEtale.RestrictedCoefficientMate.restricted_coefficient_mate_projection` from the existing flat coefficient normalization and internal scalar mate projection theorem. Private helpers identify the actual scalar mate using Mathlib's iterated-mate equivalence, the ordinary pullback monoidal structures, the two derived tensor comparisons, and the degree-zero regular-coefficient comparison. The final proof computes the adjunction transpose and uses tensor naturality. Existing public signatures, definitions and public imports are preserved. New imports are proof-only. Checked the new import directions for cycles. The proof is uniform in the identity morphism, identity coefficient map, zero complex and zero coefficient ring; it uses no nonzero-coefficient assumption or cancellation of a non-isomorphism.

## Proved and sorry left

The original hole is in `AlgebraicGeometry.ProEtale.RestrictedCoefficientMate.restricted_coefficient_mate_projection`. Closed that one hole; added zero holes. The module contains zero `sorry`, and no statements were split off. The complete proof compiled cleanly through the project compile server (40.1 seconds); delivery checks run with this packet.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`. The separate direct application of the ring-sheaf-change transpose theorem and the section projection transport theorem is subsumed by the already stated `internal_scalar_mate_projection`, itself already in the dependency closure of flat coefficient square normalization. The direct proof dependencies `lem-weil-pbc-ring-sheaf-change-adjunction`, `lem-weil-pbc-ringed-projection-mate-exact`, and `lem-sfb-internal-scalar-pullback-normalization` are replaced by the existing `lem-sfb-internal-scalar-mate-projection` and its normalization input. Their declarations and dependencies remain needed by that theorem and are not withdrawn. The direct tensor-complex inverse calculation is unnecessary: the existing `leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison` proves the required equality. No source declaration is removed. The obsolete top-level `tool_uses` entry for `lem-weil-pbc-ring-sheaf-change-adjunction` is withdrawn because the proof no longer invokes that tool directly; its existing consumers remain intact.

## Where the brief, the DAG or earlier work was wrong

The planned tensor identification is not definitional: `ModuleRingedComparison.internalDelta` uses the mate-induced `internalPullMonoidal`, whereas `leftDerivedUpperStarTensor` uses `CondensedRing.monoidal_upperStar`. The existing proved private equality of the oplax structures, and injectivity of `Monoidal.toOplaxMonoidal`, identify them. The two regular-coefficient identifications likewise require the exact-localization single-complex coherence maps. These are proof glue, not statement or definition changes.

No public signatures, attributes, definition bodies or public imports were changed. No source-library modules were modified.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
