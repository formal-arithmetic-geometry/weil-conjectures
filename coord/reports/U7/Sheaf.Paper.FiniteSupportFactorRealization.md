## What changed

Replaced the hole in `Sheaf.Paper.FiniteSupportFactorRealization` by an explicit
assembly from finite composition, proper normalization, and open normalization.
The private `cancel_witness` proves the categorical cancellation of the retained
input witness. `support_composition_factor` constructs a bounded-below etale-origin
witness using the existing `finiteRealization_etaleOrigin`, applies the actual
`finiteCompositionNormalization`, and cancels the witness. `factor_realization`
then applies the two operation identity normalizations through the generic
`cancel_factor` naturality calculation.
The public theorem applies this calculation to the prescribed identity square.
Its statement, public imports, and definitions are unchanged.

Validation: both modules compiled successfully through `lcompile.py`; the final
item compile exited zero. The original public signature was also checked verbatim,
the DAG dependency lists match the unions of their proof-step uses, and no profiling
options or debugging traces remain.

The remaining coefficient-only identity-factor compositor evaluation is stated
in the new module `Sheaf.Paper.FiniteSupportIdentityFactorCompositor`. It has no
supplied `SixFunctorFiniteOperations`, operation realizations, constructible input,
or integral reductions. It is the geometric subcalculation inside the original
plan, rather than another statement of the finite-operation conclusion.

## Proved and sorry left

Closed the original body hole in
`WeilConjectures.FixProjectionCompactification.finiteSupportFactorRealization`
(node `lem-sf-finite-support-factor-realization`). The item module has zero holes.
The four private assembly lemmas have complete proofs.

Added one hole:
`WeilConjectures.FixProjectionCompactification.finiteSupportIdentityFactorCompositor`
(node `lem-sf-finite-support-identity-factor-compositor`). This is a decomposition:
one original hole closed, one strictly smaller coefficient-only hole added; no net
hole reduction is claimed. All remaining finite-operation normalization and witness
transport work is proved in the item module.

## No longer needed

No existing public import was removed. The proof does not use
`lem-sf-finite-support-origin-binary-normalization`, implemented by
`Sheaf.Paper.FiniteSupportOriginComparison.originSupportComparison_composition`.
Instead it applies `finiteCompositionNormalization` directly at the retained
witness, avoiding the round trip through canonical origin-support coordinates.
The original plan's remaining identity-factor evaluation must still be supplied
in either route, and it is now the explicitly separate coefficient-only equation.
The binary normalization node remains available for its other consumers.
No module is withdrawn; no blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The stated binary normalization dependency is not the complete identity-factor
evaluation: it establishes composition after transport to canonical origin-support
coordinates. Proper/open unit evaluation of that compositor and its coefficient
realizations is additional work. The delivery isolates precisely that geometric
step and proves the finite-operation assembly, including construction and
cancellation of its witness. The rework row mentions a quarantined version importing
`SfP1ProjectionTraceFalseTail`; the current item source is present, preserves its
Lean attachment, and has no such import. No quarantine archive is removed.

## New nodes

`lem-sf-finite-support-identity-factor-compositor` records the canonical coefficient
compositor on the identity-proper compactification of an open immersion followed
by the identity-open compactification of a proper map. The target compactification
is exactly the pair of factors. Its source is the original operation-stage
normalizations and the proper/open compatibility paragraph of
`prop-sf-pf-coherence.proof.md`. The docstring and node give the proof through site
comparison, identity adjunction triangles, and cancellation of the two retained
witness maps. The statement covers arbitrary etale-origin witnesses, including
zero and the empty open. LeanSearch, LeanFinder, Loogle, and source/Mathlib grep found only
generic naturality/unit identities and the existing constructions, without this
evaluation equation. No existing module or definition is changed.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
