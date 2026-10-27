## What changed

Proved `WeilConjectures.FixProjectionCompactification.integralProjectionProperFactorReduction`
from the existing support-coordinate theorem and the existing completed tensor/pullback
reduction square. The proper part is a private, proved adjunction calculation: transport
those tensor and pullback comparisons into the supplied exchange-stage coordinates, apply
`map_rightAdjointProjectionMap_comp_mateEquiv`, identify its mate with `directReduction`
using the counit formula, and cancel the tensor-source transport. The main theorem pastes
this square with support coordinates using tensor and proper-projection naturality.

The module adds proof imports of `IntegralProjectionSupportFactorCoordinates`,
`IntegralProperTensorPullbackReduction`, and the source library's `ProjectionMapMate`.
A private irreducible component wrapper, with proved component and naturality equations,
keeps the doubly curried proper projection from unfolding during endpoint comparisons.
Only the assigned module and its node are changed. All existing statement signatures
and public imports are preserved.

Validation: `lcompile.py` accepted the complete module and the unchanged direct
importer `Sheaf.Paper.IntegralProjectionReductionNormalization`, including the
per-file time gate. Profiling options and temporary validation modules were removed
before delivery.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.FixProjectionCompactification.integralProjectionProperFactorReduction`.
No holes are added and no holes remain in the delivered module. The proper-coordinate
helper and all categorical helpers are proved privately in that module.

## No longer needed

No original import is removed and no module is withdrawn. The direct proof-dependency
edges to `def-fix-six-functor-datum`, `lem-sf-generator-reduction-coherence`, and
`lem-coef-integral-residue-tor` are unnecessary for this proof. The normalized support
coordinate theorem and tensor/pullback square supply the needed comparisons directly.
`def-sf-operation-stages` is retained for its normalization equations. No declaration
or module of the adopted source library is removed, and the unit route is preserved.
The separate generator-reduction and residue-Tor lemmas are not imported directly.

## Where the brief, the DAG or earlier work was wrong

The first planned step is already proved as `integralProjectionSupportFactorCoordinates`.
The second can be obtained from `integralProperTensorPullbackReduction` and the general
categorical mate square; it does not need another unfinished normalization theorem.
The finite-Tor hypothesis of the original statement is preserved, though commutativity
of this proper-factor coefficient square does not use it.

The categorical theorem `lem-sp-categorical-projection-mate-square` is used as a proved
general adjunction tool. It is not a smooth-purity argument and bypasses no unit step.
Its specified comparisons are supplied by the completed tensor square and the existing
coordinate constructions.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
