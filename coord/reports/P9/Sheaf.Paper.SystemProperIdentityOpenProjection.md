## What changed

Prove `WeilConjectures.IntegralProjectionReduction.systemProperIdentityOpenProjection`
without changing its signature or any public definition. Add four private proof imports:
`SystemPushIdentityPullUnit`, `IntegralSystemCompositorAssociativity`,
`IntegralSystemTensorComposition`, and `RefinementProjectionWords` under
`Sheaf.SixFunctors`.

The identity-pair unit fixes the canonical pullback identity. The tensor-composition
law at the identity pair forces its tensor normalization; compositor associativity
extends the identity-pair unit to an arbitrary map. A categorical calculation of the
inverse open projection's transpose gives open cancellation. First-variable naturality
of the proper projection then proves the stated compactification equation.

The private categorical unit and transport arguments are adapted from the existing
proofs in `RefinementProjectionLocalTensor`; the bridge calculation follows
`SystemPushIdentityPullUnit`. Every helper is proved. Update the item's own DAG node
to record the actual supporting lemmas. No other existing module or node is changed.

Validation: `lcompile.py` compiled the completed proof in 25.5 seconds. Its only
warning requested an explanatory comment for the local heartbeat setting; that
comment is included. The delivery runs the final compile and axiom probe.

The identity-unit and tensor-composition lemmas belong to `sk-thm-sf-compatibility`.
They are used as generic coherence tools for the actual system operations, not as
replacement statements for any unit. The item's unit has no realized statement or
steps to bypass, and its proper-coincidence route is retained.

## Proved and sorry left

Closed one of one original holes:
`WeilConjectures.IntegralProjectionReduction.systemProperIdentityOpenProjection`
(node `lem-sf-system-proper-identity-open-projection`).

Holes added: zero. Holes left in the delivered module: zero. No split-off statements.
The argument uses existing system-level declarations, including their actual specified
adjunctions, tensor comparisons, and compositor. It makes no assumption about faithful
finite evaluation or good systems.

## No longer needed

None. No existing import was removed, and neither original declared dependency is
pruned. The unit route is preserved. The additional imports provide already proved
identity-unit, associativity, tensor-composition, equality-transport, and naturality APIs;
no further coefficient normalization statement is introduced.

## Where the brief, the DAG or earlier work was wrong

The original node named only definitions as proof dependencies. The proof can close
using the already proved identity-pair pullback unit, tensor-composition compatibility,
and compositor associativity. Its updated proof dependencies now name these explicitly.
No mathematical statement or definition was repaired or weakened.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
