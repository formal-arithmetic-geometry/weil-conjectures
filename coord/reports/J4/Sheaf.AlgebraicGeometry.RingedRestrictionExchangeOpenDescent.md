## What changed

Reduced `AlgebraicGeometry.Scheme.RingedRestrictionExchange.open_restriction` to the
ordinary inverse-image cube through the proved helper `restriction_exchange_cube` in
`Sheaf.AlgebraicGeometry.RingedRestrictionDerivedCube`. The item applies that helper
and unfolds its original `pullSquare` abbreviation. The helper applies the existing
`Functor.mapDerivedCategory_exactCube`, identifies all six faces by
`ambientSquare_localization`, and takes the four specified derived mates using
`exchangeMate_cube`. The four side comparisons are inverted as required by the
original theorem statement. The helper has no openness hypothesis and no local holes.

Added `Sheaf.AlgebraicGeometry.RingedRestrictionPullbackCube`, containing the remaining
ordinary compositor coherence assertion. This assertion concerns modules and exact
inverse-image functors only: it has no complexes, derived direct images, exchange
transformations, or open immersion hypothesis. It is a strict part of the original
argument, not a renamed exchange assertion. Its docstring and node record the
sectionwise conjugation and fibre-product uniqueness argument.

The localization helper takes ordinary square comparisons as arguments. Four private
face equations normalize the shared-coefficient functor presentations. The private
`TypedDerivedCube` structure gives all comparisons, exchanges and adjunctions their
shared-vertex types; `cube_data` constructs it from the specified data. A proved
normalization wrapper for `exchangeMate_cube` substitutes the four named exchange
transformations before specialization. The mate-cube proof keeps this package abstract
and only then substitutes `cube_data`; this avoids expensive kernel expansion of the
concrete comparisons. All helpers are local to the item; no shared definition is changed
and no construction uses an arbitrary unproved witness.

The item's new imports are private proof imports. All existing declarations,
statements, definitions, attributes and public imports are preserved. No other existing
Lean module is changed, so no consumer adaptation or change record is required. The
parent node's step 7, proof dependency union and proof origin follow the implemented
route. The blueprint unit route is preserved.

The optimized proof first compiled together with the item in 47.9 seconds. A delivery
compile took 67 seconds and was refused before any push. The proved cube helper was
therefore factored into its own module, leaving the original item with a short
application. The final `lcompile.py --all` then compiled the ordinary cube module in 4.2 seconds,
the proved derived-cube helper in 31.0 seconds, and the item in 47.4 seconds. All
files are below the 60-second limit. No profiler options or scratch modules remain.

## Proved and sorry left

One of the three original holes is closed by decomposition:
`AlgebraicGeometry.Scheme.RingedRestrictionExchange.open_restriction`.
Its combination proof and the entire new `RingedRestrictionDerivedCube` module contain
no `sorry`. The latter is a proved performance factorization, not another split-off
hole or an assertion admitted under a new name.

Two original holes remain unchanged in the item, both attached to
`lem-sf-ringed-restriction-exchange-open-descent`:

- `AlgebraicGeometry.Scheme.RingedRestrictionExchange.openCube_exists`.
- `AlgebraicGeometry.Scheme.RingedRestrictionExchange.identity_normalization`.

One hole is added in the new module:
`AlgebraicGeometry.Scheme.RingedRestrictionExchange.restriction_pullback_cube`,
attached to `lem-sf-ringed-restriction-pullback-cube`.

Thus the item goes from three holes to two; the delivery has three holes in total.
This is one decomposition, with net zero holes closed, not a claim of a complete
sorry-free proof. No definition contains a new hole. The ordinary cube has been checked
for orientation, coefficient types, identity faces, zero modules and empty schemes;
none needs an extra hypothesis.

## No longer needed

No existing import, module or node is pruned. No original import was removed; the new
localization and mate proof imports now belong to the proved helper module.

Step 7 no longer needs a separate resolution comparison argument, K-injectivity of
restricted resolutions, or substitution of the open counit equation. The old step's
nodes `lem-pur-kinjective-restrict-localized-universes`,
`lem-weil-pbc-proetale-ringed-open-comparison`,
`lem-weil-pbc-site-morphism-composition`, and
`lem-sfb-proetale-open-restriction-counit` remain needed elsewhere in this module's
proof plan; they are not withdrawn. The new ordinary cube still uses site composition
coherence. The exact-localization and mate-cube theorems are reused instead of restating
or reproving them.

## Where the brief, the DAG or earlier work was wrong

The old step 7 described a resolution-level proof. The already proved generic
`DerivedExactCube` and `ExchangeMateCube` APIs give a shorter formal reduction: only
ordinary inverse-image compositor coherence remains. There is no statement dispute,
new geometric assumption, or change to target statements.

## New nodes

`lem-sf-ringed-restriction-pullback-cube`, in
`dag/nodes/sec-six-functors/lem-sf-ringed-restriction-pullback-cube.json`, records the
ordinary six-face inverse-image cube equation. It is stated in
`lean/Sheaf/AlgebraicGeometry/RingedRestrictionPullbackCube.lean`. Sources are Stacks
sites.tex Tag 03CB and proetale.tex Tag 09A5; the proof plan is the ordinary
compositor-coherence part of the parent's step 7. The statement applies to any
`OpenCube` and every module, with no openness or derived-category input.

`lem-sf-ringed-restriction-derived-cube`, in
`dag/nodes/sec-six-functors/lem-sf-ringed-restriction-derived-cube.json`, records the
proved localization-and-mate argument in
`lean/Sheaf/AlgebraicGeometry/RingedRestrictionDerivedCube.lean`. It has zero local
holes and uses the ordinary cube node plus the existing exact-localization,
canonical-square-normalization and mate-cube theorems. The item now depends on
this helper node in step 7. This file split preserves the argument while keeping
its optimized implementation separate from the item's other proofs.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
