## What changed

Proved WeilConjectures.PurScalarProjection.diagram_projection and
WeilConjectures.PurScalarProjection.ordinaryCompletedSquare in the assigned module.
The finite diagram equality is the existing ordinary compact-support coefficient
square mapped through the whole derived reduction functor and postcomposed with
nativeRealization. The ordinary F inner tensor is constructible by pull_domains
and tensor_domains; the integral residue-Tor criterion supplies its finite-Tor witness.

For ordinaryCompletedSquare, compactSupportCoefficientModels_scalar supplies the
scalar-extended constructibility domains. The existing integral_ramification helper
supplies a positive exponent and the required principal-ideal equation. Precompose
with scalar extension of the invertible source completion unit. The existing
projection_unit equations, naturality of comparison and of completionUnit, and the
scalarCompletion unit equation reduce the result to the ordinary coefficient square
followed by compact support of the F inner completion unit. Cancellation gives the
completed equality. The new proved private scalarTensorCompleted_unit records the
outer tensor version of that same unit equation.

Added proof-only imports of CompactSupportProjectionCoefficientChange,
CompactSupportCoefficientModels, and all CompletedIntegralFiniteFree. Moved
projection_unit before ordinaryCompletedSquare and diagram_projection after it to
respect their proof dependencies. Local irreducibility attributes keep the specified
coefficient maps and scalar comparisons abstract while elaborating. Existing public
signatures, visibility, definitions and public imports are preserved. The item node
records the actual proof routes. No other Lean module is changed.

Validation: the complete final Lean module compiled cleanly through lcompile.py
in 41.3 seconds, with no errors or warnings. A declaration-header comparison
confirmed every existing signature and all public imports are unchanged; the
DAG proof dependencies equal the union of its proof-step uses. No new proof
imports create a path back to the item.

## Proved and sorry left

Closed 2 of the 8 holes in the item source read at the start of this session:

- WeilConjectures.PurScalarProjection.diagram_projection
- WeilConjectures.PurScalarProjection.ordinaryCompletedSquare

Added 0 holes and split off 0 statements. The six unchanged local holes, all attached
to lem-pur-compact-support-scalar-projection-identification, are:

- WeilConjectures.PurScalarProjection.scalarCompletion_existsUnique
- WeilConjectures.PurScalarProjection.properProjection_existsUnique
- WeilConjectures.PurScalarProjection.openProjection_existsUnique
- WeilConjectures.PurScalarProjection.realization_existsUnique
- WeilConjectures.PurScalarProjection.native_scalar_identification
- WeilConjectures.PurScalarProjection.gamma_identification

The imported compactSupportProjectionCoefficientChange is an existing named theorem
hole of lem-pur-compact-support-projection-coefficient-change. It is not a new hole.
The proofs also use the existing scalarCompletion_existsUnique normalization.
This is a partial delivery for a module with multiple holes, with two complete
proof bodies from existing named dependencies.

## No longer needed

No Lean import, module, declaration or DAG dependency is withdrawn. The generic
ordinary coefficient square is already among this item's recorded dependencies.
For diagram_projection the independent representative-level finite diagram proof
and the previously recorded cancellation argument are unnecessary: functoriality
of the native reduction suffices once the ordinary equality is available.
For ordinaryCompletedSquare the actual invertible constructible source unit
suffices; no complete-target Hom bijection is needed for this square.
The broader completion, proper/open, and strict scalar-mate dependencies remain
needed by the six other local comparison obligations and are retained.

## Where the brief, the DAG or earlier work was wrong

The source file read at the start had eight theorem holes, including diagram_projection
and ordinaryCompletedSquare, although the DAG and the earlier K7/N4 reports already
recorded proofs of these two declarations. This packet proves both against the actual
current source and records the six remaining holes honestly.

The new diagram proof is shorter than either the original ringed-diagram argument
or the earlier completion-unit cancellation route. It applies a functor to an
integral equality, so it never assumes faithfulness of reduction or finite evaluation.
The arguments include identity scalar extensions, zero inputs, and empty schemes;
no positive-rank cancellation or projection invertibility is used. The unit's
coefficient-compatibility route remains intact.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
