## What changed

Replaced the proof of `WeilConjectures.compactSupportProjectionCoherence_common`
without changing its signature. The pentagon is proved directly from the finite-stage
pentagon, the four binary composition squares, naturality, and cancellation of the
support-comparison isomorphism. This calculation is generic in the coefficient functor.

For the other three equations, the proof constructs the two sides as natural
transformations, passes both inputs to their finite coefficient compositum with
`isoToStage`, applies the corresponding finite-model equation, and transports the
result back by naturality. The tensor/projection compatibility calculation on the
included finite models remains in three separate new modules, imported only for the
proof. These lemmas fix one field, two models and one equation, rather than restating
the whole common-stage theorem. The original node now records this proof.

Validation: all four modules compiled through `lcompile.py`; the original module
compiled without warnings in 33.2 seconds against the three new modules.

## Proved and sorry left

The original module had one hole, in
`WeilConjectures.compactSupportProjectionCoherence_common`; its proof is now complete.
The pentagon transport, naturality of both projection mates, and descent of equality
from common-field models to arbitrary pairs are proved without additional holes.

Three holes are added, each the whole proof of one public theorem:

- `WeilConjectures.commonProjectionCompactification_onStage`
  (`lem-sf-common-projection-compactification-on-stage`).
- `WeilConjectures.commonProjectionComposition_onStage`
  (`lem-sf-common-projection-composition-on-stage`).
- `WeilConjectures.commonProjectionProper_onStage`
  (`lem-sf-common-projection-proper-on-stage`).

This is a decomposition: one original hole replaced by three strictly smaller,
independent finite-model equations. It is not a net decrease in holes. No hole remains
in the original module, in a private helper, or inside a definition.

## No longer needed

No original public import is removed, and no module is withdrawn.
The parent's proof no longer directly uses
`def-weil-derived-pullback-tensor-hom` or
`def-pur-completed-pullback-tensor-comparison`; those are needed by the three
finite-model comparison calculations and remain their proof dependencies.
No underlying dependency is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The pentagon does not require tensor normalization, the projection formula, or an
extra threefold comparison theorem. It follows from the four existing binary
coefficient-comparison squares and naturality. One input also needs no coefficient
enlargement: it is literally included from its own stage.

The remaining calculations are isolated on actual finite models. Their statements
include no separatedness assumption on the structure morphisms. Identity maps,
repeated fields, empty schemes and zero objects use the same functorial and adjunction
identities; the split statements introduce no nonzero or faithful-inclusion premise.

## New nodes

`lem-sf-common-projection-compactification-on-stage` is the refinement equation for
models included from a single finite field. Its source is the coefficient
compatibility paragraph and the projection coherence sentence.

`lem-sf-common-projection-composition-on-stage` is the binary composition equation on
those models, including the specified final pullback compositor. It has the same
source and keeps every endpoint comparison.

`lem-sf-common-projection-proper-on-stage` is the proper-counit equation on those
models, with the actual proper identification. It has the same source.

Each node has its own module, complete proof in words, and recorded searches.
No existing public signature or definition changes, so no change record or consumer
adaptation is necessary.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
