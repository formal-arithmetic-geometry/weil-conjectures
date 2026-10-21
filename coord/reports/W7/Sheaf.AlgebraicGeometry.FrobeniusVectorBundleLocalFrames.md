## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.frobenius_vectorBundle_local_frames` with a proof of its
same mathematical statement. Pull finite local freeness back to the etale test scheme,
refine a free trivialization to an affine neighbourhood, and reindex the basis
by `ULift (Fin n)`. Pull the frame to each etale object, use the normalized tensor
comparison to obtain linear coordinates, and remove the universe lifts.

Naturality is proved through surjective evaluation from `etaleHom`, evaluation
naturality, pseudofunctor composition, and the existing finite free coordinate
naturality theorem. Scalar compatibility follows from linearity. Private helpers
are all proved; the frame and coordinate definitions contain no holes. The proof
also covers rank zero and does not require extra nonemptiness assumptions.

Added private proof imports of
`WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent` and
`WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeCoordinatesNaturality`.
Updated the existing node's proof and proof dependencies to describe this route.
The Lean presentation now shares the structural morphism, etale composition
functor, and existing scalar action in explicitly typed transparent local lets.
Expanding those lets gives the original hypotheses, witnesses and equations;
no assumption or conclusion is changed. This prevents conversion from unfolding
tensor pullback. A generic proved postcomposition lemma transports evaluation to coordinates
without an expensive rewrite through concrete tensor sections. Local irreducibility
of the tensor comparison, structure-sheaf comparison and free-pullback comparison
keeps their data abstract during conversion. No heartbeat limit is changed.
Normal-limit verification and all consumer checks are recorded below. No public import or
source-library definition changed.

Adapted the unclaimed direct consumer
`Sheaf.AlgebraicGeometry.FrobeniusVectorBundleLocalCoordinates`: preserve the
frame's transparent lets through a private helper and perform the semilinear
calculation using an abstract additive group. Its existing matrix-coordinate
argument is retained. The result explicitly names the same localization base S.
In the unclaimed `Sheaf.AlgebraicGeometry.FrobeniusVectorBundleAffineKernelModels`,
name S in the private coordinate hypothesis and align local instance priorities;
its public theorem and scheme construction are unchanged.

Change records:
`coord/changes/frobenius-local-frames-scalar-sharing.md`,
`coord/changes/frobenius-local-coordinates-base-sharing.md`, and
`coord/changes/frobenius-affine-kernel-localization-base.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.frobenius_vectorBundle_local_frames`
(node `lem-weil-pbc-frobenius-vector-bundle-local-frames`).
Added 0 holes; split off 0 statements; 0 sorries remain in any delivered Lean file.
The consumer adaptations retain their complete proofs and add no assumptions.
The frame theorem's axiom check uses only `propext`, `Classical.choice`, and
`Quot.sound`. The final standalone axiom check passed in 13.4 seconds.
The first delivery dry run passed; its repeated inline axiom probe reached the
60-second timeout. The standalone check of the completed public theorem covers
all helpers it uses and confirms there is no imported sorry or additional axiom.

## No longer needed

Removed the private import
`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` and the direct proof
edge to its node `def-pc-module-pullback`. Its separate section-adjunction wrapper
is unnecessary: the proof uses the existing abstract module pullback API and the
normalized tensor comparison already provided by the tensor-section modules.
This does not assert that other consumers of that module can be removed.

No other planned nodes or modules are pruned. In particular, the evaluation
naturality dependency remains needed. The existing free-coordinate naturality
node `new-sbc-pullback-free-coordinates-naturality` is reused rather than splitting
off another coordinate comparison theorem. The blueprint unit's realized steps
are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is valid. Its reference to tensor composition can be
implemented using the existing abstract pullback coordinates and normalized
comparison; it does not require the separately imported section-adjunction
wrapper. The inline scalar formula was hard to use because its conversion
unfolded tensor pullback. Sharing the same expression in transparent local lets
repairs this performance problem without changing its mathematical meaning.
The downstream checks and necessary adaptations are recorded below.

The resumed dispatcher reference clock changed from start timestamp
1792446345 to 1792499211.494496; the sandbox also contains attempt briefs
`.brief2`, `.brief3`, `.brief4`, and `.brief5`, with no explicit attempt identifier
in `.budget`. This metadata was left untouched, and proof work continued.

## Forced adaptations

All four downstream consumer modules are unclaimed in the shared claim snapshot
and in `coord/claims` and `coord/rework.tsv`. The dependency-use search lists
LocalCoordinates as the sole direct user of the frame theorem, and lists
LocalLifts and AffineKernelModels as direct users of LocalCoordinates; Kernel is
their remaining downstream consumer.

LocalCoordinates: the original proof fails against the repaired frame interface
with `(deterministic) timeout at whnf`, at the normal 200000-heartbeat limit.
Its eager frame unpacking lost sharing of the scalar action and made conversion
unfold tensor pullback. The local attributes and four proved private helpers
keep that action and localization shared, while preserving the existing matrix
argument. The public proof uses the helper instead of the original inline
semilinear calculation. The only explicit public signature edit names `(U := S)`
in the existing localization. This is the same base that was previously inferred.

AffineKernelModels: the original proof times out at 60 seconds against the new
coordinate interface; matching the local instance paths alone still times out.
The private `affineKernelModelsOfCoordinates` hypothesis now names `(U := S)`
in its localization, and local category/section-module instance priorities match
the producer. No public theorem text, proof of representability, finite-cover
construction, import or visibility changes.

Normal-limit compile results (all clean, no warnings):

| module | seconds | result |
|---|---:|---|
| FrobeniusVectorBundleLocalFrames | 23.4 | compiled |
| FrobeniusVectorBundleLocalCoordinates | 0.1 | compiled; earlier fresh compile 10.5 |
| FrobeniusVectorBundleAffineKernelModels | 9.1 | compiled |
| FrobeniusVectorBundleLocalLifts | 28.8 | compiled unchanged |
| FrobeniusVectorBundleKernel | 7.8 | compiled unchanged |

The delivered LocalCoordinates adaptation changes local attributes at lines
30-35, adds proved private helpers at lines 101-194, explicitly names S at line
228, and replaces the public proof at lines 242-245. AffineKernelModels changes
only local attributes at lines 31-34 and the private localization base at line
172. All other declarations and proofs in that module are retained. Unchanged
verification copies of LocalLifts and Kernel were removed from the packet; they
are not withdrawals.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
