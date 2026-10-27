## What changed

Restored `lean/Sheaf/Paper/QuotientSectionTensorNormalization.lean` from its
quarantine archive for the rework assignment. The recorded failure is the
`DerivedCategory.Q.LaxMonoidal` typeclass timeout in `TensorNormalized`.
Selected the existing named internal-module instance caches locally, importing
`Sheaf.Paper.IntegralResidueDerivedMonoidal` privately. `TensorNormalized` now binds the existing
`Mod.laxMonoidalQ` instances for the two module categories explicitly before
its unchanged equation, bypassing the failing search. Public signatures,
canonical data, public imports, and the mathematical proof route remain unchanged.

The final unprofiled single-file compile passed in 31.0 seconds with no
warnings and the original heartbeat limits and transparency options.

The preserved direct consumer `Sheaf.Paper.QuotientPullbackTensorCoherence`
compiled unchanged against the repair in 59.6 seconds, with no warnings. Its
temporary source copy was removed from the sandbox after this check.

Change record: `coord/changes/A3-quotient-section-tensor-elaboration.md`.

## Proved and sorry left

This is the assigned compilation repair. Closed 0 holes; added 0 holes.
The one existing hole remains in
`AlgebraicGeometry.ProEtale.QuotientSectionTensor.quotient_section_tensor_normalization`
(node `lem-sfb-quotient-section-tensor-normalization`). Its source and complete
nine-step natural-language argument remain in its docstring and DAG node.
No definition contains a hole.

## No longer needed

None. No declaration, module, dependency, or import is withdrawn. In particular,
the quarantined item is restored, and its retained DAG parents still need it.

## Where the brief, the DAG or earlier work was wrong

The current item is absent from `lean/` because it was quarantined after a
build failure, not because its mathematics was withdrawn. The rework row names
the preserved archive and the typeclass timeout at `TensorNormalized`. This
repair uses the same existing instances through local named caches; it adds no
hypothesis and changes no comparison map. No DAG correction or new node is needed.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
