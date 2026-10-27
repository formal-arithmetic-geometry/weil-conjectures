## What changed

In `Sheaf.Paper.CanonicalTateArrowNaturality`, proved the ordinary scalar-module
comparison existence-and-uniqueness lemma. The coefficient comparison is the conjugate of the
restriction-of-scalars/direct-image comparison. Their section formulas follow
from the conjugate-unit identity; uniqueness follows from the composite
adjunction bijection. Private helpers identify the actual scalar-extension unit with the published tensor section.
Existing public statements, definitions and public imports are unchanged.
The existing node records the preliminary scalar adjunction argument and its three
existing API dependencies, while retaining the nine-step main-theorem plan.

## Proved and sorry left

Closed one of the three original holes:

- `WeilConjectures.CanonicalTate.ordinaryScalarSquare_existsUnique`.

Two original holes remain unchanged:
`WeilConjectures.CanonicalTate.ordinarySquare_existsUnique` and
`WeilConjectures.CanonicalTate.canonicalTateArrowNaturality`, attached to
`lem-pur-canonical-tate-arrow-naturality`. Their source and proof descriptions
remain in their docstrings and node. No holes were added or split off. The completed
comparison lemma use existing library theorems, including their stated
normalizations; this does not assert that all transitive dependencies are proved.

## No longer needed

No nodes or modules are withdrawn. The nine-step proof plan for the remaining
main theorem is retained. Removed the following unused or transitively public
private imports (no public import changed):

- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage`.
- `Sheaf.Paper.ProEtaleCoefficientModulePullbackComposition`.
- `Sheaf.AlgebraicGeometry.RootsOfUnityInverseImageIso`.
- `Sheaf.Paper.PurIntegralTwistLineInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`.
- `Sheaf.Paper.IsomorphismDerivedPullback`.
- `Sheaf.Paper.PurTwistSheafLocallyFree`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`.
- `Sheaf.Paper.DerivedPullbackTensorIso`.
- `Sheaf.Paper.CompletedOperationTowerSubstitution`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`.
- `Sheaf.Paper.IntegralOperationsWellDefined`.
- `Sheaf.Paper.DerivedPullbackTensorHom`.
- `Sheaf.Paper.ShiftedTensorMorphismCalculus`.

The briefly added explicit import of
`Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction` was also removed,
since its APIs are already publicly available.
`Sheaf.SecSmoothPurity.CochainCoefficientArrows` is the sole new private proof
import; it supplies the normalized scalar-extension adjunction. APIs from the
removed imports that are already publicly imported remain available transitively.
Removing an unused proof import while the main proof is unfinished is not a claim
that its node can be withdrawn.
The unfinished spatial comparison and the main theorem retain their existing
proof dependencies. No node is claimed pruned merely because the corresponding
proof import is currently unused.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The ordinary coefficient comparison
can be proved directly using the existing adjunction and direct-image APIs,
without constructing an additional tensor associator by hand. The completed scalar
proof preserves the required unit-section normalization, including arbitrary
scheme morphisms and finite coefficient extensions.

The node additionally cites `def-pur-integral-compact-support-coefficient-data`,
`def-pur-cochain-coefficient-arrows`, and
`def-weil-pbc-ring-restriction-pullback-comparison` for the exact completed
coefficient square, scalar-adjunction, and sectionwise direct-image APIs used. These
are existing generic coefficient/module tools, not replacements for any step
of the package unit. No new nodes or maintainer tool approvals are introduced.

The attempted spatial conjugacy proof encountered costly elaboration of
site-object equality transport and composite module units. It was not retained
as a claimed closure; the original spatial theorem and its source/proof docstring
remain unchanged.

Validation: the module compiled through the required server compiler in 40.6
seconds with the scalar proof complete. Temporary profiling and declaration
markers were then removed. Existing public signatures and public imports match
the original verbatim; no new public declarations or changed definitions.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
