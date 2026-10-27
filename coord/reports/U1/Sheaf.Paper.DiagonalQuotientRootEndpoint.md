## What changed

Proved `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalQuotientRootEndpoint`
with its original signature. Its quotient projection is constructed explicitly:
annihilation factors the coefficient quotient through the positive ell-power
level, and the scalar-extension adjunction transposes that level projection.
The free-module unit gives the exact root equation.

Added `Sheaf.Paper.DiagonalQuotientRootProjectionIso`, containing
`diagonalQuotientRootProjection_isIso` and proved private helpers. The normalized
projection is epic because the free-module image of the epic root-tower projection
factors through it. Its source and target have rank-one bases on the same
compatible-root cover. An epic endomorphism of the regular module over a
commutative ring sheaf is invertible, so the projection is an isomorphism.
The finite-root basis argument adapts the proved cyclic-tensor and sheaf tensor
comparison helpers from `SpRootBasisLevel` to arbitrary annihilated coefficients.

The initial combined projection module compiled cleanly in 34.1 seconds, but a
later preflight exceeded the per-file limit. Its two independent proved arguments
are now extracted as `DiagonalFiniteRootBasis` and `DiagonalLocalRankOneIso`, each
with its own public theorem and node. All profiling options are removed.
The complete four-module packet compiled cleanly with `lcompile.py --all`.

The endpoint module transports the free-module universal property through the
supplied realization. The Cartier line has the same universal property by its
etale construction and the comparison adjunction. The two universal properties
construct inverse maps and fix the root unit. Naturality supplies the requested
normalization after composing with the quotient projection.

All added imports are proof imports. No existing public import, statement,
definition, attribute or source-library declaration is changed. The positive
completed-coefficient and root-projection route of the unit is retained.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalQuotientRootEndpoint`
(node `lem-diagonal-quotient-root-endpoint`).

Added and proved
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalQuotientRootProjection_isIso`
(node `lem-diagonal-quotient-root-projection-iso`). Also added and proved `diagonalFiniteRootBasis`
and `diagonalLocalRankOne_isIso`. All private helpers are proved.
There are zero `sorry` declarations in the delivered Lean files and zero holes
split off. This is a proof, not a decomposition into new admitted statements.

## No longer needed

No original public import was removed and no module is withdrawn.
The endpoint's planned direct dependencies
`lem-poincare-compatible-primitive-roots`
(`Sheaf.PoincareDuality.CompatiblePrimitiveRoots`) and
`lem-amb-tate-root-projection-reduction`
(`Sheaf.Paper.AmbTateRootProjectionReduction`) are replaced in its node by the
proved internal quotient-projection theorem. The new proof uses the normalized
root cover already packaged in `tateTwist_finite_locallyFree` and only the local
surjectivity clause of `rootTower_finite_tensor`. This avoids transporting the
entire alternative `SheafOfModules` coefficient presentation and its reduction
coherence. These modules may remain needed by other consumers; no whole-library
pruning is claimed.

An exploratory proof import of `ProEtaleTateTwists` was removed from the new
module. Its common-cover theorem includes rational and algebraic-closure clauses
that are unnecessary here. The finite root cover, prescribed integral basis and
slice scalar-extension basis suffice.

## Where the brief, the DAG or earlier work was wrong

The endpoint statement is correct and unchanged. The original root-projection
reduction theorem uses different module and coefficient presentations, so it
cannot simply be applied to `quotientLine`. The new argument constructs the
actual internal module projection rather than leaving an encoding comparison
as a further obligation.

The original proof plan's regular-unit normalization is unnecessary for this
particular endpoint: the realization equivalence and underlying-sheaf comparison
already transport the free-module universal property, including its root unit.
No hypotheses are weakened or discarded from the existing declaration.

Edge cases checked in the argument are n=0 (the exponent is l), a zero coefficient
ring, an empty scheme, and ramified quotients. Only the stated annihilation is
used; neither flatness nor a ramification-index divisibility assumption is added.

## New nodes

`lem-diagonal-quotient-root-projection-iso` records the proved invertibility of a
specified root-normalized internal module projection. It contains no realization,
Cartier-line endpoint or ordinary-site comparison. Its proof is the epic
factorization and local rank-one argument described above. The new node has its
source, full proof steps, three actual Mathlib searches and exact Lean attachment.
`lem-diagonal-finite-root-basis` records the cyclic tensor calculation for an
arbitrary annihilated internal coefficient sheaf.
`lem-diagonal-local-rank-one-iso` records the local epic rank-one criterion.
Both statements are proved, and both are proper parts of the projection argument.
No change record is needed: only the assigned module, its proof node, and the new
modules and their nodes are changed.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
