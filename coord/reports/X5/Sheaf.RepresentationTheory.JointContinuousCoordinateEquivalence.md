## What changed

Proved `ContinuousCohomology.exists_jointContinuousCoordinateEquivalence` in
`Sheaf.RepresentationTheory.JointContinuousCoordinateEquivalence`, preserving its
statement. Constructed the exact submodule of continuous equivariant functions,
the cumulative-product linear map, and its successive-ratio inverse. Continuity
uses `continuous_pi`, induction with `Fin.partialProd_succ`, and joint continuity
of the given action. The inverse identities use Mathlib's
`Fin.partialProd_left_inv` and `Fin.partialProd_right_inv`, together with the
homogeneous equivariance condition. This follows all eight existing proof steps;
the finite-product arguments include degree zero without extra hypotheses.

Removed the redundant private import `Mathlib.Topology.Order`.

Validation: the complete proof compiled through `lcompile.py`; final delivery
also runs the server compilation and axiom probes.

## Proved and sorry left

Closed 1 of 1 original holes:
`ContinuousCohomology.exists_jointContinuousCoordinateEquivalence`
(node `lem-sfb-joint-continuous-coordinate-equivalence`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.

## No longer needed

Removed private import `Mathlib.Topology.Order`; its initial-topology API is
already available through the retained Mathlib imports. The proof uses the
finite-product specialization `continuous_pi` of the planned initial-topology
criterion. Both existing DAG dependencies, `lem-weil-pbc-initial-topology-continuity`
and `def-weil-field`, remain relevant. No nodes or modules are withdrawn, and no
additional Sheaf proof dependencies are needed.

## Where the brief, the DAG or earlier work was wrong

None. The existing plan and statement agree with the implemented proof. The
noncommutative group order is preserved throughout, and no compactness,
separation, local compactness, or discreteness assumptions are used. The unit
route is unchanged. No new nodes or consumer adaptations are necessary.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
