## What changed

Filled three theorem proofs in `Sheaf.Paper.CompactSupportCondensedRealizationSetup`:
`scalarModelTransport_subsingleton`, `scalarModelTransport_nonempty`, and
`encodingRestriction_existsUnique`, in namespace
`WeilConjectures.CompactSupportCondensedRealization`.

The ordinary scalar models are compared through their specified change-of-rings objects
and maps, after identifying the completed coefficient maps by their residue normalization.
Sheafification and tensor extensionality establish ordinary uniqueness. The existing exact
completed tensor model and its universal counit give the derived comparison; cancellation
of that invertible counit on complexes proves derived uniqueness.

The encoding restriction comparison is constructed as the identity on sections. The
section-ring map normalization and the inverse chart equations identify its scalar actions.
Sectionwise extensionality proves uniqueness.

The item imports `Sheaf.Paper.OperationScalarTransportNormalization` and
`Sheaf.Paper.NormalizedSectionEncodingRestriction` only for their proofs. The former
constructs and proves the scalar transport, using the small universal-counit API in
`Sheaf.Paper.CompletedScalarTransportCounit`. All three new modules have complete proofs.
All existing public signatures, definition bodies, attributes, and public imports remain
unchanged. The reconstruction definitions are marked locally irreducible after their
construction block to prevent repeated unfolding in later declarations; this does not
change the reducibility seen by any importer. The unused proof import
`Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars` is removed.

Updated the item's DAG proof and dependencies, with a node for each proved helper module.
No other existing module is changed. No change record is necessary.

Validation: profiling identified repeated elaboration and typeclass inference through
large reconstruction composites. Generalizing the section proof, hiding the completed
scalar construction behind its counit API, and keeping the reconstruction API locally
irreducible reduced the item compile to 22.4 seconds on the project server. The preceding
server check compiled the three helper modules in 36.6, 2.2, and 49.2 seconds. Every file
is below the 60-second limit, with no compiler diagnostics. Profiling options are removed.

## Proved and sorry left

Original holes: 6. Closed: 3. Added: 0. Remaining: 3. This is a proof delivery, with no
split-off obligations.

Closed, all in namespace `WeilConjectures.CompactSupportCondensedRealization`:

- `scalarModelTransport_subsingleton`.
- `scalarModelTransport_nonempty`.
- `encodingRestriction_existsUnique`.

Remaining, with their original signatures and docstring proofs unchanged, all attached to
`lem-pur-compact-support-condensed-realization-setup`:

- `WeilConjectures.CompactSupportCondensedRealization.fieldExtension_flat`.
- `WeilConjectures.CompactSupportCondensedRealization.omegaExtension_flat`.
- `WeilConjectures.CompactSupportCondensedRealization.realizedCoefficient_square`.

The scalar constructions apply to identity embeddings, zero modules, and empty scheme sites:
no nonzero or nonempty assumption is introduced. The section identities also cover empty
test objects. No targets or statement hypotheses are changed.

## No longer needed

Removed the unused proof import `Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars`.
Its preservation theorem is not used by the completed proofs. No module or node is withdrawn. The three outstanding assertions still need
the original coefficient-flatness and normalized coefficient-chart dependencies. The unit
route and all existing public imports remain in place. The proof reuses the already proved
completed scalar model and counit rather than introducing any new intermediate obligation.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement discrepancy was found. The two completed coefficient-map names
are separately defined choices, so they must first be identified by their common finite
projection normalization. The previous prose did not make that Lean transport explicit.
The existing completed scalar exact-model API supplies the required derived counit
comparison directly. The ordinary encoding square needs only the section-ring definition
and inverse chart equations, without a new geometric comparison theorem.

## New nodes

`lem-pur-normalized-section-encoding-restriction`: the completely proved general
identity-on-sections restriction comparison, in `Sheaf.Paper.NormalizedSectionEncodingRestriction`.
This module has zero holes and contains a completed proof,
not a split-off obligation. No change record is needed.

`lem-pur-completed-scalar-transport-counit`: the completely proved derived
comparison and its computation-counit equation, in `Sheaf.Paper.CompletedScalarTransportCounit`.
This theorem applies the existing completed tensor model and its counit theorem.
Its proof-only import hides that construction's additional instances from the item.
It adds zero holes.

`lem-pur-operation-scalar-transport-normalization`: the fully proved existence
and uniqueness results for OperationScalarTransport, in
`Sheaf.Paper.OperationScalarTransportNormalization`. The ordinary comparison is
constructed and uniquely normalized on pure tensors; its derived comparison is
constructed from the existing exact model and uniquely normalized by the counit.
Both theorems have complete proofs and add zero holes. The original item's
statements retain their names, binders, and attributes and apply these proved results.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
