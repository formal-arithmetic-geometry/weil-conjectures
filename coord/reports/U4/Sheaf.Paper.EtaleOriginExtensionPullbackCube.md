## What changed

Proved `AlgebraicGeometry.ProEtale.etaleOriginExtensionPullbackCube` in
`Sheaf.Paper.EtaleOriginExtensionPullbackCube` without changing its signature.
Added proof-only imports of `EtaleOriginRestrictionPullbackCube`,
`FiniteOpenScalarRealizationTransport` and `EtaleProEtaleScalarMateData`.
The latter two are imported with `all` to reuse their proved private normalization
lemmas. Three proved private helpers identify scalar mates and their whiskering.
Updated the item node to record the actual adjunction-mate argument.

The proof first derives the mate of the intrinsic site/scalar comparison from the
existing realization coefficient-unit equation. It then pastes scalar mates of the
site and geometric comparisons, uses the existing restriction cube, and cancels
the scalar/pullback isomorphisms. It applies to arbitrary unbounded inputs.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.etaleOriginExtensionPullbackCube`
(node `lem-fix-etale-origin-extension-pullback-cube`).
No holes remain in the item and no holes are added or split off.
The proof uses the existing stated restriction cube, whose proof remains an
independent existing obligation; this delivery does not claim its axioms are closed.

Validation: `deliver3.py` runs the final remote single-file compile and stage-3
preflight before pushing this packet. Earlier compiler checks of the proof took
13.9 to 18.7 seconds, below the 60-second file limit.

## No longer needed

No existing imports were removed. No modules are withdrawn.
The original plan's separate ordinary balanced-tensor and K-flat-resolution
calculation is unnecessary here: the proof reuses the normalized coefficient
comparisons and obtains the extension cube by mates of the restriction cube.
The direct proof dependency on `lem-weil-pbc-ring-sheaf-change-adjunction` is
replaced by the defining FourCorners inverse-mate equation. Its module remains
needed transitively, as do the original definition dependencies; no deletion of
these modules or their declarations is requested.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The DAG planned independent resolution computations
for the two cubes, but the scalar-adjunction normalization makes the extension cube
a formal consequence of the restriction cube. The existing proved private
`realization_scalar_unit` and `scalarPullbackEtaleIso_eq_fromMate` lemmas supply
the necessary normalizations, so a third split of the obligation is unnecessary.
The unit's statement and route are preserved.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
