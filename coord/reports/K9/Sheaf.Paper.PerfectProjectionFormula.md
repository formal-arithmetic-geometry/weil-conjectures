## What changed

Proved `AlgebraicGeometry.Scheme.PerfectProjection.totalization_compatibility` from the
mixed representative projection mate and the specified signed-total inverse. Added the
independent theorem `AlgebraicGeometry.Scheme.proEtaleMixedProjectionMate`, proved using
flat resolutions, the tensor-pullback representative equation, and the normalization of
the derived counit. Its proof does not assume a perfect coefficient or a projection inverse.
The new concrete definition `AlgebraicGeometry.Scheme.proEtaleProjectionTotal` gives the
ordinary signed total mate an explicit complex type. Its data is the existing
`tensorAdjunctionTotal` construction. Private categorical lemmas handle naturality,
transport, and adjunction injectivity.
Existing pure tensor helper proofs now use the already proved representative API.

The local opacity settings prevent unfolding chosen mixed isomorphisms, the canonical
tensor comparison, and the signed total mate in categorical equations. A proved helper
exposes the tensor comparison equation without unfolding its choice in the main proof. These proof-context commands are recorded in
`coord/changes/K9-perfect-projection-proof-context.md`. Existing public signatures,
definitions, instances, and public imports are unchanged. No consumer adaptation is needed.

## Proved and sorry left

Closed one of the item's three original holes:
`AlgebraicGeometry.Scheme.PerfectProjection.totalization_compatibility`.
The new theorem `AlgebraicGeometry.Scheme.proEtaleMixedProjectionMate` is proved; it
adds zero holes. This is one hole closed, zero holes added, and zero unfinished split-offs.

The original holes retained, both attached to
`lemma-weil-pbc-perfect-projection-formula`, are:

- `AlgebraicGeometry.Scheme.PerfectProjection.perfect_projection_formula`;
- `AlgebraicGeometry.Scheme.PerfectProjection.baseChange_compatibility`.

No definition contains `sorry`. Both modules compiled in import order: the mixed-mate
module in 57.4 seconds and the item in 52.1 seconds, with no warnings. The delivery
checks the final packet and the axiom report.

## No longer needed

No imports, nodes, or modules are pruned from the item: its two remaining original
proofs still need their recorded dependencies. For the totalization calculation, the
same-universe `RingedTensorCorner` exact-mate interface is unnecessary. The proof uses
the existing independent-universe tensor pullback interface and the new mixed-mate lemma.

## Where the brief, the DAG or earlier work was wrong

The exact-mate corner interface cannot be instantiated directly on the original
pro-etale site, whose object and morphism universes differ. The mixed calculation
retains the original sites and avoids that interface. The item DAG now records this
additional representative-normalization dependency. The former missing dependency
artifact is no longer the failure encountered by compilation in this session.

## New nodes

`lem-weil-pbc-proetale-mixed-projection-mate`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-proetale-mixed-projection-mate.json`,
states the localization formula for the counit mate on arbitrary flat K-flat coefficient
representatives. Its module is `Sheaf.Paper.ProEtaleMixedProjectionMate`; its proof
follows Stacks 07A4, 07A6 and 0B56. It is strictly independent of the bounded splitting,
isomorphism and inverse assertions of totalization compatibility. Searches of Mathlib,
the source library, and Sheaf are recorded in the node. The proof-context change record
is `coord/changes/K9-perfect-projection-proof-context.md`.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
