## What changed

Restored `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePreBase`
from its quarantined interface by publicly re-exporting its complete adopted
source implementation. Consolidated the duplicate Sheaf normalization and
comparison-helper modules with their corresponding source implementations.
These two additional modules were unclaimed. Every original public import is
preserved, and every public declaration remains available at its existing
Sheaf import path. No source-library file is modified.

The legacy `AlgebraicGeometry.affineTildeFunctor` now abbreviates
`affinePushforwardTilde`; both reduce to the same associated-sheaf functor.
Its zero-map instance reuses the canonical instance. The concrete normalization
and tensor-comparison maps are unchanged. The three normalization nodes now
attach to the adopted source declarations; their mathematical statements,
proof plans, dependencies and unit realization are preserved.

The change record is
`coord/changes/W2-affine-tilde-source-prebase-rework.md`.

## Proved and sorry left

This is a zero-hole definition/interface repair. The archived item has zero
`sorry`s; the restored item and both adapted modules have zero. Holes closed:
none. Holes added: none. Split off: none. There are no remaining holed declarations
in the delivery.

The complete adopted source implementations supply
`AlgebraicGeometry.affineTildeTensorOrdinarySourceIso`,
`AlgebraicGeometry.affineTildeTensorDerivedCounit`,
`AlgebraicGeometry.affineTilde_scalarExtension_comparison`, and
`AlgebraicGeometry.affineTilde_pushforward_unit_isIso`. This is reuse of existing
proofs and data, not a claim of four newly closed holes.

All three compatibility modules compile through `lcompile.py`. A separate
consumer checks all four complete archived public types, using the legacy
tilde abbreviation and the current additive scalar-extension witness; it
compiled in 47.3 seconds. Its `#print axioms` output for all four declarations
contains only `propext`, `Classical.choice` and `Quot.sound`.
A diagnostic rebuilding both old data constructions and comparing them by
`rfl` exceeded 60 seconds; it is not claimed as a passing check. The data
comparison instead uses the complete implementation comparison described below.
The unchanged `AffineBaseChangeTildeRepresentative` consumer also timed out
at 60 seconds both against the repaired interface and, separately, against
the unmodified published baseline. No adaptation of that consumer is delivered.
The unchanged `AffineTildePushforwardHomologyFactorization` consumer compiled
against the repaired interface in 43.6 seconds. The unchanged
`AffineTildeCoefficientPushforwardHomologyCoordinates` consumer timed out
at 60 seconds both against the repaired interface and against the unmodified
published baseline. These consumer sources are not part of the delivery.
The required delivery dry run passed compilation and preflight; its review
class is CODEX because the compatibility interfaces re-export existing public
declarations from their adopted source modules.

## No longer needed

No mathematical dependency, node or module is withdrawn. The duplicate local
proofs and data definitions are replaced by their complete source implementations.

The item no longer directly imports these proof modules:

- `Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel`;
- `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonHelpers`;
- `WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso`;
- `Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit`;
- `WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso`;
- `Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde`;
- `WeilConjectures.AlgebraicGeometry.TensorPullbackTilde`;
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`;
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`.

The normalization interface no longer directly imports
`WeilConjectures.Algebra.Homology.AffinePushforwardCohomologyEdgeExists` or
`WeilConjectures.Algebra.Homology.AffinePushforwardCohomologyEdgeIsIso`.
Their results remain used by the adopted normalization proof. The helper module
has no removed imports. All original public imports of the three modules remain.
No unit route is pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned module was quarantined after a duplicate `derivedPullback`
import, not withdrawn. A direct import repair additionally required the current
scalar-extension additivity name, the intended sheaf universe, and removal of
a repeated irreducibility attribute. Although this direct repair compiled
initially, its delivery compilation exceeded the single-file limit while
rechecking duplicate constructions. The library already contains the complete
same argument and concrete definitions, so consolidation removes the repeated
checking without splitting a proof or changing the argument.

A full implementation comparison, ignoring whitespace, is identical for all
three modules after the tilde-abbreviation substitution, the obsolete additive
witness replacement, the corrected abelian universe annotation, and removal
of the repeated irreducibility attribute. The last three substitutions apply
only to the prebase module; the other implementations differ only in the
tilde abbreviation and whitespace. The additive proof replacement is proof
irrelevant, and both tilde abbreviations reduce to the same functor. No false
statement, weakened conclusion, arbitrary replacement map, or unit-route error
was found. The quarantine archives are preserved.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
