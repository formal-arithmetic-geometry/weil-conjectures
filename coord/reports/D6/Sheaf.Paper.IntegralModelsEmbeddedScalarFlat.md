## What changed

Proved `AlgebraicGeometry.ProEtale.integralModelsEmbeddedScalarFlat` from the existing
spectral integral scalar flatness theorem and the existing embedded scalar-square
comparison. The target signature is unchanged. Added only private proof imports
and two proved private helpers: `scalarFlat_transport` transports local relation
factorizations across a commuting square of ring isomorphisms; `smallRingIso`
reconstructs a small-site ring isomorphism from an internal ring isomorphism.
Updated the node's proof, proof dependencies, and proof origin to this route.
The single-file server compile passed without warnings in 19.0 seconds.

## Proved and sorry left

Closed one of one existing holes:
`AlgebraicGeometry.ProEtale.integralModelsEmbeddedScalarFlat`
(node `lem-sfb-embedded-integral-scalar-flat`). No holes remain in the item, and no
new holes or split-off statements were added. The proof uses existing named
statements `IntegralModelsStacks.integralModels_flat_residue` and
`embeddedIntegralScalarKernelSquare`, whose unfinished proofs remain their own
items. This delivery does not assert that their transitive axioms are closed.

## No longer needed

No existing imports were removed, and no modules were withdrawn.
The direct completion route is unnecessary for this item: it does not directly
use `lem-weil-l-adic-extension-integers-dvr`,
`det-prop-sfb-qlbar-colimit-x-integral-limit`,
`sk-prop-sfb-qlbar-colimit-x`, or
`det-prop-integral-criterion-constant-coefficients` as proof dependencies.
Their work is not globally pruned: the spectral flatness theorem and existing
public imports may still need it. The spectral/embedded comparison remains used,
through its proved concrete ring-sheaf comparison. The pointwise PID alternative
and generic inverse-image flatness development are not imported.

The relation-criterion and tensor-comparison nodes are existing proved tools from other units:
`lem-weil-pbc-flat-local-relations-universes` and
`lem-exc-site-local-relations-imply-flat`, and
`lem-weil-pbc-independent-sheaf-tensor-colimits`. They supply the general site flatness
criterion; the integral-models unit has no separate replacement for that general
criterion. The already listed coefficient-comparison node is also from
`sk-lem-int-ext`. No `tool_uses` approvals were edited.

## Where the brief, the DAG or earlier work was wrong

The planned completion argument is valid but need not be repeated for embedded
coefficients. The library already has spectral flatness and the underived scalar
square required for its transport. The unit's flatness step is retained.
The item source was initially absent from the shared local snapshot, with no
rework/quarantine row; its current server source was recovered read-only before
editing. No definitions, public statements, or other modules were changed.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
