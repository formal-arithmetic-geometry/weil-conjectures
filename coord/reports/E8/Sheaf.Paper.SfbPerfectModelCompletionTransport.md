## What changed

The original completion equivalence now follows from the canonical coefficient-ring
comparison, the commuting residue-projection square, the resulting equality of kernel
ideals, a comparison of cochain complexes, and the existing restriction-of-scalars
completeness theorem. The original theorem signature and docstring are unchanged.
Its new proof imports are
`SfbPerfectModelComplexComparison`, `FlatRingedIdealCompleteEquivalence`, and
`ProEtaleOperations` (the last with `import all` for its proved module equivalence).

`SfbCompletionRingComparison` constructs the constant-sheaf, quotient-diagram and
completed-ring isomorphisms and proves compatibility with every finite projection.
These are actual constructions using sheafification compatibility and preservation of
limits. The item module proves the kernel-ideal calculation directly using the local
membership description of extension of ideals. Its private `completeIso` proves
invariance of completeness under derived isomorphism.

`SfbPerfectModelComplexComparison` isolates the constant-module/scalar-extension
identification. Its statement is a cochain isomorphism,
with no completeness hypothesis or conclusion. This is step 2 of the original argument,
strictly part of the completeness comparison, rather than the original obligation
under another name.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.Scheme.sfbPerfectModel_completion_transport` is replaced by a complete
Lean proof from the complex comparison and the existing scalar-restriction theorem.
The new ring comparison and all private helpers are proved. The private generic
`mapPreimageIso` combines the localization-preimage isomorphism and the exact derived
functor factorization; the item module applies it to the small-site module equivalence.
The application explicitly fixes the coefficient-size sheafification instances,
category structures and localization universes; no transparency option is disabled.

One hole is added:
`AlgebraicGeometry.Scheme.sfbPerfectModel_complex_comparison`, node
`lem-sfb-perfect-model-complex-comparison`, in
`Sheaf.Paper.SfbPerfectModelComplexComparison`.

This is a decomposition: 1 original hole reduced to 1 strictly smaller cochain
comparison, with net hole closure 0 among the delivered declarations.
No definition contains a hole.

## No longer needed

No existing module is withdrawn. All original mathematical dependencies remain needed,
either directly or through the complex-comparison node. The restriction-of-scalars
argument uses the proved `siteDerivedRestrictScalars_locallyDerivedComplete_iff` API
from `FlatRingedIdealCompleteEquivalence`, which itself proves the bridge from the
original restriction-local-completeness theorem to the exact derived functor.

The final proof does not import `CompletedKoszulConstantTransport` or
`CompletedConstantCoefficientEquivalence`. Its kernel calculation is self-contained,
and the latter's private comparison uses a different `AsSmall` universe.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically unchanged. Its generic sheafification and scalar
restriction dependencies do not themselves identify the two particular coefficient
complexes. That identification is now a separate precise statement. The ring comparison
must use `AsSmall.{u+1}`, matching the target's coefficient-sized site.

The comparisons are valid for unbounded complexes, zero rings, I=0, I=A, and the empty
scheme: there is no perfectness, Noetherianity or nonemptiness hypothesis in either
new statement.

## New nodes

`lem-sfb-completion-ring-comparison`: the constructed canonical completed-ring
isomorphism and its projection equation, in `Sheaf.Paper.SfbCompletionRingComparison`.
Its proof has no holes.

`lem-sfb-perfect-model-complex-comparison`: the cochain comparison between the
transported actual model and restriction of the normalized model, in
`Sheaf.Paper.SfbPerfectModelComplexComparison`. This is the one remaining hole, with
the full original constant-module and scalar-extension argument in its docstring.
Localization-preimage transport is proved
in the item module itself.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
