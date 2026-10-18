## What changed

Proved `AlgebraicGeometry.Scheme.smooth_connected_curve_local_rings` in
`Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`, preserving its signature
byte for byte and preserving all public imports. Added the fully proved private
helper `AlgebraicGeometry.normalized_dvr_valuation` for the algebraic part.

The proof obtains Noetherianity and regularity from finite type and smoothness,
then integrality from connectedness. Mathlib supplies the generic stalk's field
structure, injective germ and stalk maps, and fraction-field instances. A closed
generic point would make the curve a singleton of dimension zero. The proved
source-library dimension-one complement lemma makes every nongeneric point closed.
Coheight bounds make each closed stalk one dimensional, hence a DVR.

The normalized valuation is explicitly constructed as minus the logarithm of the
maximal-ideal adic valuation. Mathlib's unit-times-integer-power decomposition gives
existence; applying the valuation gives the exponent and cancellation gives the
unit's uniqueness. Powers of an irreducible give surjectivity. Mathlib's DVR
valuation-subring characterization gives the nonnegative-value equivalence.
The construction precedes the choice of uniformizer, giving independence.

Added proof-only imports of `WeilConjectures.Mathlib.Topology.KrullDimension` and
`Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`. Updated the
existing node's proof, proof dependencies and proof origin to match this route.
No public definition, existing signature, target or consumer was changed.
The unit `sk-def-pic` has no realized steps to bypass; its route is preserved.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.smooth_connected_curve_local_rings`
(node `lem-sc-smooth-connected-curve-local-rings`).
Added 0 holes; split off 0 theorems. No `sorry` remains in the delivery.
The private helper is fully proved. The module compiles through `lcompile.py`.

## No longer needed

Removed the proof-only import `Sheaf.AlgebraicGeometry.Dimension`: the argument
uses `topologicalKrullDim` directly, so neither `Scheme.dim` nor its comparison
with topological dimension is required. Removed proof dependency `def-pc-dimension`;
its module `Sheaf.AlgebraicGeometry.Dimension` is not needed by this proof.

Removed proof dependency `def-weil-regular-scheme` and did not import its module
`Sheaf.AlgebraicGeometry.IsRegularScheme`: the existing source-library `IsRegular`
class and the independent local Noetherian instance suffice, without the wrapper.

Removed the redundant proof-only direct import
`WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`; its DVR theorem remains
used and is available through `WeilConjectures.AlgebraicGeometry.Regular`, so its
node `lem-sc-regular-dim1-dvr` remains a proof dependency. All other original
proof dependencies remain used, directly or through the recorded instance and
fraction-field APIs. These are direct dependency removals; no claim is made that
other target paths cease to import these modules.

## Where the brief, the DAG or earlier work was wrong

The statement is correct and unchanged. The original plan reconstructs two results
that already exist: `IsOpen.isClosed_singleton_of_mem_compl` in the source library
(node `lem-sc-dim-one-point-outside-open-closed`), and Mathlib's fraction-field
unit-times-zpow decomposition and DVR valuation-subring characterization. Reusing
them eliminates the separate local-dimension wrapper and the hand-built comparison
of uniformizers. No new nodes or statement repairs were necessary.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
