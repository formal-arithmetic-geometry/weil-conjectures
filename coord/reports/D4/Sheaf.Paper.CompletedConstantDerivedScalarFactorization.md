## What changed

Proved `AlgebraicGeometry.Scheme.completed_constant_derived_scalar_factorization`
in `Sheaf.Paper.CompletedConstantDerivedScalarFactorization`, preserving its full
statement and both public imports. Added only private proved helpers and private
proof imports; no shared definition, instance or interface changes.

The proof identifies the coefficient square on limit projections, proves that the
given beta is the profinite inverse-image isomorphism, and uses the existing natural
ordinary constant-module inverse-image comparison. Noetherian completion quotient
isomorphisms and completed-constant-algebra flatness make extension along phi exact.
The universal derived functor is therefore its exact derived-category functor.
Restriction equivalences and uniqueness of left adjoints transport derived scalar
extension through the coefficient square. Exact-functor composition finishes the
comparison for all unbounded complexes.

Updated the item's DAG proof, proof dependencies and proof origin to this route.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.completed_constant_derived_scalar_factorization`.
Added 0 holes, split off 0 statements, and left 0 holes in the delivered module.
Every added private helper has a complete Lean proof.

## No longer needed

The item no longer directly needs the planned K-flat composition dependency
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
(`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`) or the separate planned dependency
`lem-pur-derived-change-of-rings`
(`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`). The exact extension and adjunction route replaces
that step. General scalar-extension infrastructure remains available through
`BoundedConstructibleTower`; this is not a claim that its underlying foundations
or either node are globally unused.

No original imports were removed: the two public imports are required by the
unchanged statement. No existing module is withdrawn or deleted, and no unit-level
statement or proof step is bypassed. The exploratory proof import
`Sheaf.Paper.NormalizedTowerLissePropagation` was removed: its small formal
coefficient-transport argument is proved locally using `ProEtaleOperations`.

## Where the brief, the DAG or earlier work was wrong

The original plan does not need a new K-flat-resolution comparison here. The
completion is Noetherian, its extended-ideal quotients are the original quotients,
and the existing flat-algebra theorem makes scalar extension exact. This permits
a direct proof with existing declarations, without a sixth split of the obligation.
No statement defect or tool workaround is used.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
