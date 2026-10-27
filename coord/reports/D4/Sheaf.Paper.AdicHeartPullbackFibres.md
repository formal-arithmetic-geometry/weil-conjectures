## What changed

Completed four existing proofs in `Sheaf.Paper.AdicHeartPullbackFibres`, with every public
signature and definition unchanged. `base_properties` and `base_geometric_properties` use
Mathlib noetherianity and compactness and the source library's direct finite-type dimension
bound. The stalk unit is the image of the base-field unit through global sections and the
germ map. `integralPull_mem` transports bounded constructible finite reductions through
actual completed pullback, following the proved `pbcQbarIntegralPull_mem` argument for arbitrary
finite coefficient fields. `pullFamily_existsUnique` specializes the existing uniquely
normalized PBC pullback family; proof irrelevance identifies the integral membership proofs.
Private proof imports expose those established reduction and descent declarations.

The four-proof version compiled cleanly in 57.7 seconds (exit 0). Subsequent attempts to
verify further proofs failed before Lean startup with `No space left on device` while
`stdbuf` created a temporary directory. Those unverified experiments are outside the delivery,
in the sandbox scratchpad. The final delivery retains the four validated proofs only.

## Proved and sorry left

Closed 4 of the original 7 holes; added 0 holes and split off 0 statements.

Proved (all names below are in `AlgebraicGeometry.Scheme.PerAdic`):

- `base_properties`
- `base_geometric_properties`
- `integralPull_mem`
- `pullFamily_existsUnique`

The 3 unchanged holes are:

- `fiber_existsUnique` (blueprint `lem-per-adic-heart-pullback-fibres`)
- `commonT_existsUnique` (blueprint `lem-per-adic-heart-pullback-fibres`)
- `adicHeartPullbackFibres` (blueprint `lem-per-adic-heart-pullback-fibres`)

No target is claimed axiom-free: the remaining assertions and imported unfinished lemmas
remain on the target dependency route. This is a partial proof delivery, not a decomposition.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`:
`AlgebraicGeometry.exists_topologicalKrullDim_le` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType` directly bounds the base
scheme, including the empty scheme. No passage through its sole scheme-theoretic fibre is
needed. Updated step 1, proof dependencies, proof origin and the obsolete tool-use entry of
`lem-per-adic-heart-pullback-fibres` accordingly, citing `lem-kun-dimension-finite-type`.
Other modules can still use the general fibre-dimension theorem; no module is withdrawn.
The other existing planned proof imports remain for the unchanged main proof hole.

## Where the brief, the DAG or earlier work was wrong

The original geometric proof plan used a general uniform fibre-dimension theorem where
an already proved dimension bound for finite-type schemes over fields applies directly.
The normalized completed pullback family already exists in `PbcQbarCompletedPullback`.
No statement, definition, unit route, source-library declaration or public import changed.
The compiler infrastructure subsequently failed before Lean startup (exit 125) because
it could not create temporary directories. This is unrelated to the Lean time limit.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
