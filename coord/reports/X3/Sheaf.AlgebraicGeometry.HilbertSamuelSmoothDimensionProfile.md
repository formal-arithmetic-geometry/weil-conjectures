## What changed

Completed four proofs in `Sheaf.AlgebraicGeometry.HilbertSamuelSmoothDimensionProfile`.
All existing statements, definitions, attributes and public imports are unchanged.
The finite-difference operators are proved inverse and lexicographic order preserving and
reflecting, including all iterates. The dimension-profile finiteness theorem uses Mathlib's
Noetherian local-ring theory and Artinian maximal-ideal-power quotients. The modified-head
formula uses the stalk coheight bound and iterated cancellation. Presentation equivalence
is proved in both directions by induction on finite test depth, retaining existence and
universality of transforms.

Added six proved private helpers for these arguments. Added private Mathlib imports for
Krull's height theorem, finiteness of minimal primes and finite-set infima. Updated the
item node's proof descriptions and proof origin to record the implemented arguments;
the remaining geometric proof plan and its dependency list are retained.

Validation: single-file remote compilation through lcompile.py; delivery also runs the
standard axiom probe and mechanical checks. No shared module interface was changed.

## Proved and sorry left

Closed 4 of the original 13 holes, with no added holes or split-off statements:

- `AlgebraicGeometry.HilbertSamuel.integer_operators`.
- `AlgebraicGeometry.HilbertSamuel.dimension_profile_finite`.
- `AlgebraicGeometry.HilbertSamuel.modifiedHead_eq`.
- `AlgebraicGeometry.HilbertSamuel.modified_presentation_equivalence`.

The following 9 original theorem proofs remain exactly `by sorry`, all attached to
`lem-trf-hilbert-samuel-smooth-dimension-profile`, with their existing source and complete
proof docstrings:

- `AlgebraicGeometry.HilbertSamuel.smooth_dimension_profile`.
- `AlgebraicGeometry.HilbertSamuel.normalizedHead_regular`.
- `AlgebraicGeometry.HilbertSamuel.modifiedHead_properties`.
- `AlgebraicGeometry.HilbertSamuel.local_modified_presentations`.
- `AlgebraicGeometry.HilbertSamuel.modified_presentation_history_comparison`.
- `AlgebraicGeometry.HilbertSamuel.center_locallyConstant_iff`.
- `AlgebraicGeometry.HilbertSamuel.modifiedHead_nonincrease`.
- `AlgebraicGeometry.HilbertSamuel.modifiedHead_no_infinite_drops`.
- `AlgebraicGeometry.HilbertSamuel.modified_presentation_empty_maximum`.

This is a partial proof delivery, not a decomposition. None of the four completed proofs
uses any of the remaining nine holes, or any other theorem with a postponed proof.

## No longer needed

Removed these unused private imports from the item:

- `Sheaf.RingTheory.SmoothLocalTangentConeExtension`.
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`.
- `WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence`.
- `Sheaf.RingTheory.RegularSequenceGradedPolynomial`.
- `WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg`.
- `WeilConjectures.RingTheory.FiniteTypeDomainDimensionTrdeg`.
- `Mathlib.RingTheory.Filtration`.
- `Mathlib.RingTheory.Spectrum.Prime.Topology`.

The four completed proofs need none of the geometric dependencies above. In particular,
local dimension finiteness and the local modified-head formula do not need finite-type
domain transcendence-degree calculations. These nodes still occur in the plans of the
nine open clauses, so their DAG edges are retained. No module or node is withdrawn or
claimed globally unnecessary; no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The node's proposed finite-type domain dimension calculation is unnecessary for
`dimension_profile_finite` and for the local formula `modifiedHead_eq`: Noetherian local
rings already have finite dimension, and the local stalk dimension is bounded by the
scheme dimension. This is a shorter proof of those clauses, with unchanged hypotheses
and conclusion. The remaining global profile comparison still uses the original plan.
No false statement, interface defect or process failure was found.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
