## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isAmple_tensorPullback_tensorPow_of_relative`
with its existing signature. All added helpers are private and proved in the item module.
This repairs the return of head `37a2a2c09`: removed the duplicate private theorem
`AlgebraicGeometry.Scheme.Modules.tensorPullback_invertible`, added the proof-only import
`Sheaf.AlgebraicGeometry.BertiniIncidenceNaturality`, and replaced all five uses by
`AlgebraicGeometry.bertiniTensorPullback_invertible`. Its explicit scheme, morphism,
module and invertibility binders agree exactly with the removed helper. The imported
result is generic preservation of invertibility under pullback; the proof uses no Bertini
incidence result. The DAG now records this dependency. Current main still has the original
public theorem with one sorry, and the retained proof and node edits remain applicable.

The proof follows Stacks Morphisms Tag 0892(1): establish qcqs, clear denominators,
synchronize finitely many affine section loci at an explicit exponent, and use eventual
global generation to obtain the entire tail. No definitions or statements changed.

Compared the explicit tensor pullback to ordinary module pullback by adjoint uniqueness.
The finite-subcover bound is A = D(E+1), where D is the product of the positive local
degrees and E is the sum of the local lower bounds. This handles the empty scheme without
a separate case. The local denominator exponent may be zero; the extra exponent b is
strictly positive, and the proof checks nonvanishing both on and off the restricting open.

Private proof imports additionally expose the existing proved nonvanishing and
isomorphism helpers in AmpleIso, TensorSectionAffineOpen, NonvanishingLocusRestrict,
and NonvanishingCommonDegree. Also use NonvanishingGeneratingLocus,
NonvanishingTensorPullback and Modules.ProjectionFormula. The public imports stay intact.
The node proof, proof_deps and proof_origin now describe these actual steps.
The change record `coord/changes/relative-ample-proof-context.md` documents the proof's
added open commands and elaboration options, as required by static preflight. The only
downstream consumer, CompositionFiniteAffineTwistBounds, keeps the same theorem application
and requires no adaptation.

Validation: the repaired item compiled through lcompile.py in 8.3 seconds with
exit code 0 and no errors or warnings. The delivery tool checks all added constants
for axioms and holes. The import-direction check permits the new
proof import. The direct consumer's theorem application and all public signatures and
imports remain unchanged. Edge cases checked in the argument include empty Z or T,
zero local denominator exponent, arbitrary positive local tensor degrees, zero or negative
initial global-generation bound, and the nonnegative integer-to-natural conversion.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.Scheme.Modules.isAmple_tensorPullback_tensorPow_of_relative`
(node `lem-sfb-relative-ample-absolute-twist`).

Added 0 holes. The item has 0 remaining sorry declarations. No split-off statements,
new public declarations, or adaptations of other modules.

## No longer needed

Removed the duplicate private helper `tensorPullback_invertible`; all its call sites
now use the existing generic theorem `bertiniTensorPullback_invertible`.

Removed the proof-only import `Sheaf.AlgebraicGeometry.CoherentFiniteType`.
The structure module finite-type instance is constructed directly from the rank-one
free module and its local-generators data, so the separate conjunction definition
`pqf-def-coherent` is not used by this proof.

The former steps 2–3 involving affine intersections are replaced by the target-local
criterion for separated morphisms and composition of separated morphisms. Consequently
this proof does not use these former declared dependencies:

- `lem-weil-pbc-separated-affine-open-intersection`;
- `lem-weil-pbc-affine-scheme-qcqs`;
- `lem-weil-pbc-quasi-separated-affine-cover-criterion`.

No Lean modules are withdrawn: those three nodes are Mathlib leaves, and other users of
CoherentFiniteType retain their imports. `def-sc-invertible-module` stays a statement
dependency; its proof role is supplied by the recorded invertibility and projection-formula
interfaces. No part of the blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned packet unnecessarily reproved pullback invertibility under a private name.
The existing `bertiniTensorPullback_invertible` proves precisely that fact, so the repair
imports and uses it directly as requested. No helper alias remains.

No mathematical or statement error found. The DAG's affine-intersection detour is
unnecessary because Mathlib already supports locality of separatedness on the target.
The old proof description treated the finite type of O_T as automatic; the Lean proof
supplies its finite generating family and restricts it to give actual local data.

The proof uses existing proved helpers attached to
`lem-sc-pullback-tensor-power-iso`, `lem-sc-nonvanishing-locus-restrict`,
`lem-sc-nonvanishing-iff-generates-at`, `lem-sc-nonvanishing-tensor-pullback`,
`lem-sc-tensor-section-affine-open`, and `lem-weil-pbc-nonvanishing-common-degree`.
These are generic tensor/restriction/nonvanishing tools for the very section calculations
in the original plan; no special result from their owning unit is invoked. Their actual
private helper declarations are imported with `import all`, retaining upstream source
signatures and visibility. No tool_uses approvals were added or reordered.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
