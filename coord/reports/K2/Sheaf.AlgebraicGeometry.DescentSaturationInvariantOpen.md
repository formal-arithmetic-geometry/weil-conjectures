## What changed

Proved `CategoryTheory.Over.DescentDatum.exists_descentDatum_saturation_open` in
`Sheaf.AlgebraicGeometry.DescentSaturationInvariantOpen` with its statement unchanged.
Added the private proof import
`WeilConjectures.AlgebraicGeometry.EffectiveDescent.Invariant` to reuse its proved
invariant-open restriction and transport compatibility. No public API changed.

The proof computes the pullback-map image with `Scheme.Pullback.range_map`, applies
`descent_orbit_saturated` to the orbit of the source of an image witness, and obtains
`D.IsInvariant W`. It then chooses `D.restrict W hInv` and applies
`restrict_transport_left_ι`. Updated the existing node's proof and dependencies to
record this implementation of the existing route.

## Proved and sorry left

Closed one of one holes:
`CategoryTheory.Over.DescentDatum.exists_descentDatum_saturation_open`
(node `lem-trf-descent-saturation-invariant-open`).
Single-file compile passed with no warnings (1.6 seconds). The delivery preflight
checks the axiom and hole inventory.

Added zero holes. No `sorry` remains in the delivered module. No new declarations,
definitions, axioms, or nodes were added.

## No longer needed

No imports removed and no modules withdrawn. The direct construction of an
isomorphism between the two restricted pullbacks is unnecessary: the source library
already proves restriction, naturality and cocycle in transport form. Removed
`lem-weil-pbc-open-immersion-base-change` from this node's proof dependencies; the
proof does not need the open-immersion property of the two pullback inclusions.
The factorization and monomorphism nodes remain because they explain the existing
restriction construction. The orbit-saturation dependency and its tool approval
are retained. The unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The plan is valid, but its final two steps are already
implemented in `WeilConjectures.AlgebraicGeometry.EffectiveDescent.Invariant`.
Empty C gives empty W; p = identity gives W = C; the orbit argument also applies to
nonclosed points and does not impose separatedness or finiteness on V → A.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
