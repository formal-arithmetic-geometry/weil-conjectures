## What changed

Filled `AlgebraicGeometry.Scheme.pbcScalarOperations_identity` in
`Sheaf.Paper.PbcScalarOperationIdentity`. The proof first checks the ordinary
identity square on module sections and transports it through the specified
composite adjunctions. It then uses the existing cochain counit normalizations
on flat-term K-flat representatives, and naturality along a resolving
isomorphism, to obtain the derived pullback identity. An explicit mate
calculation proves the direct-image identity. Five proved private helpers
organize these calculations. The existing completed-pullback proof is retained.

Added one private proof import, `import all Sheaf.Paper.PbcActualScalarPullback`,
for the existing normalized comparison and its proved counit helpers. Existing
public imports, declaration signatures, definitions and instances are unchanged.
Updated only the item's node proof, proof dependencies and proof origin to
record this argument. No other existing module is changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.pbcScalarOperations_identity`
(node `lem-pbc-scalar-operation-unit-coherence`).
`AlgebraicGeometry.Scheme.pbcScalarCompletedPull_identity` keeps its existing
complete proof and now uses the filled theorem.

One original hole closed; zero holes added; zero textual `sorry` remain in the
item. No statement was moved to another module. Existing dependencies retain
their own proof obligations; this report does not count them as closed.

## No longer needed

No original import was removed and no module is withdrawn. The public import
of `PbcScalarOperationShift` is retained as part of the existing interface.

The item no longer directly needs the generic planned dependencies
`lem-sfb-kflat-scalar-comparison-normalization`
(`Sheaf.Paper.KFlatScalarComparisonNormalization`),
`lem-weil-pbc-finite-free-completion-transport`
(`Sheaf.CategoryTheory.FiniteFreeCompletionTransport`), or
`lem-weil-pbc-reflected-adjunction-coefficient-squares`
(`Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares`). The actual
comparison already supplies its section formula and derived counit equation;
the existing completed identity proof already uses the concrete completion
unit and hom extensionality. Their direct edges are removed from this node.
This makes no claim that those modules leave the whole targets' import closure.
The Mathlib mate dependency is used directly and retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The planned abstract normalization
route is unnecessary for this identity calculation: the existing actual
normalizations suffice. The current blueprint no longer has the node's
historical `prop-weil-pbc-scalar-extension.md` path. The proof origin now cites
the local Stacks source, Tag 0D6D, and the precise existing normalization APIs.
The unit's statement and realized proof route are unchanged.

Searches used Lean Finder, Loogle and Mathlib grep through `msearch.py`, plus
local searches of both library roots. They found the Mathlib conjugation and
mate APIs used in the proof, but no ready-made specialized scalar identity.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
