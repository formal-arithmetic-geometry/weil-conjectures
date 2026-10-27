## What changed

Filled `AlgebraicGeometry.ProEtale.IntegralModelsStacks.integralModels_flat_residue`
without changing its signature or public imports. Added proved private helpers for
constant-ring reconstruction and its scalar/residue naturality, and for transport of
finite generation, flatness and quotient kernels through ring-sheaf isomorphisms.
The continuous-ring comparison uses the existing compact-adic normalized identification;
the final algebra uses `ConstantCompletion.flat_and_quotients`.

Updated the item's DAG proof, dependencies and proof origin to record this implementation.
Only the item module and its node are changed; no definitions or statements are repaired.
All new helpers are private. The proof uses normal transparency settings.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.ProEtale.IntegralModelsStacks.integralModels_flat_residue`
(node `lem-sfb-integral-models-flat-residue`).
There are zero `sorry` occurrences in the delivered Lean file, and zero holes added or
split off. Every private helper has a complete proof. Existing dependencies such as
`compact_adic_continuous_identification` and `ConstantCompletion.flat_and_quotients`
retain their own previously stated obligations; they are not new holes in this delivery.

## No longer needed

No original import was removed and no module is withdrawn or claimed as pruned.
The direct projection-normalized integral-limit theorem
`det-prop-sfb-qlbar-colimit-x-integral-limit` is replaced as a direct proof dependency
by `lem-sfb-compact-adic-continuous-identification`, specialized using the existing
integer compactness and coset-basis theorems. Its module remains transitively imported
by existing helper modules. The integral-models unit and its completion route are retained.

## Where the brief, the DAG or earlier work was wrong

The item source was initially absent from the shared checkout although its DAG attachment
and queue row were present, and no rework/quarantine row named it. It appeared during this
session's shared refresh. The delivered statement agrees verbatim with that current source.
The DAG's mathematical plan is valid. Its categorical glue requires explicit ring-object
compatibility and scalar normalization; the proof supplies both and does not assume an
arbitrary coefficient identification.

The argument includes the empty scheme and does not assume that section rings are nonzero.
No target signature, source-library declaration, or existing public definition is changed.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
