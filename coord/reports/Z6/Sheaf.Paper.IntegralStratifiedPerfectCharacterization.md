## What changed

Proved three coefficient-interface theorems in
`Sheaf.Paper.IntegralStratifiedPerfectCharacterization`. All existing signatures,
definitions, visibility, imports, and docstrings are unchanged.

`integralCoefficientULift_exists` descends `ULift.ringEquiv` to the quotient by the
uniformizer power and proves uniqueness on quotient representatives.
`integralDetailedCoefficientComparison_exists` proves compatibility with successive
quotient maps, constructs a natural isomorphism of the actual coefficient diagrams,
and takes its limit. Preservation of the limit by forgetting commutativity is proved
through the forgetful functor to presheaves. The projection equations and uniqueness
are then proved by the limit universal property.
`integralDetailedCoefficientRestriction_exact` reflects finite limits and colimits
through the functor to underlying additive sheaves, whose composite with restriction
is the corresponding forgetful functor for the source ring.

Validation: the whole item compiled through `lcompile.py` after these three proofs.
On resumption it was compared with the current shared source; eleven newly recorded
proof imports were restored, leaving exactly the three proof replacements in the diff.
The refreshed module compiled cleanly in 6.0 seconds on 2026-10-19.
The quotient constructions also apply to zero quotient rings and empty sites; they
require no nonempty-point or nonzero-ring assumptions. The limit proof retains every
specified positive quotient projection. The exactness argument works for every ring
sheaf homomorphism, and therefore for the specified canonical isomorphism.

## Proved and sorry left

Closed 3 of the original 7 holes, with no holes added or split off:

- `AlgebraicGeometry.Scheme.integralCoefficientULift_exists`.
- `AlgebraicGeometry.Scheme.integralDetailedCoefficientComparison_exists`.
- `AlgebraicGeometry.Scheme.integralDetailedCoefficientRestriction_exact`.

Four original holes remain unchanged, all attached to
`lem-weil-pbc-integral-stratified-perfect-characterization`:

- `AlgebraicGeometry.Scheme.integralConstantModule_exact`.
- `AlgebraicGeometry.Scheme.integralStratifiedPerfectCharacterization`.
- `AlgebraicGeometry.Scheme.integralStratifiedPerfectClosure`.
- `AlgebraicGeometry.Scheme.integralStratifiedPerfectDetailed`.

The main characterization still needs the completed-constant realization exactness
and the restriction, local lifting, uniform bounds, and finite cohomology devissage
arguments described in its existing proof plan. Closure and the detailed-category
comparison retain their existing complete proof plans. This is a partial proof
delivery, not a decomposition.

## No longer needed

None. No imports removed. The unfinished theorems still need their recorded proof
dependencies, so no nodes or modules are claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The coefficient auxiliary proofs were
already described in the module docstrings and are now formalized without changing
the characterization route or the proper-base-change unit route. No new nodes,
statement repairs, definition changes, or forced adaptations.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
