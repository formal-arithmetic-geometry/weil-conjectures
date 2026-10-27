## What changed

Completed the proof body of
`AlgebraicGeometry.ProEtale.VaryingRing.derivedScalarComparison` from the existing
scalarD invertibility proof, exact localization of the open-unit equation, generic
exact-derived cube pasting, and a new ordinary alpha normalization theorem.
All existing public statements and definitions are unchanged. The proof imports
`StrictTowerOrdinaryProperOpenArrows`, `SemilinearAlphaPullback`, and the new
`SemilinearScalarOrdinaryAlphaNormalization` privately.

The ordinary alpha normalization is a separate result about ordinary strict
systems: it identifies the normalized package alpha with termwise singleAlpha.
It has its own module and node. The derived proof localizes this equality using
the existing canonical tower-alpha descent theorem. The open mate and derived
cube combination are complete proofs; no derived evaluation is assumed faithful.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.VaryingRing.derivedScalarComparison`
(node `lem-sf-semilinear-scalar-derived-comparison`): 1 of 1 original holes.
Added one hole, in
`AlgebraicGeometry.ProEtale.VaryingRing.scalarOrdinaryAlphaNormalization`
(node `lem-sf-semilinear-scalar-ordinary-alpha-normalization`).
This is a decomposition: one hole closed and one strictly lower ordinary
normalization hole added, for net zero holes. No `sorry` remains in the item
module; the new module has exactly one named theorem with `:= by sorry`.
No definition contains a hole. All private helpers in the item are proved.

## No longer needed

No original dependency or unit route is pruned. The private generic pasting
helpers imported from `SemilinearAlphaPullback` are used for exact localization;
its geometric base-change theorem is not used. The ordinary normalization node
now owns the beta/projector/compositor identification needed by the last step.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The ordinary scalar package alpha and canonical
strict-tower alpha have the same mathematical normalization, but their equality
was not stated in the library. Most of its constituent identities were written
and checked during this session: beta uniqueness by transposition, clopen
transpose, projector, open compositor, and equality transport. Attempts to join
them into the full identity repeatedly hit expensive kernel conversions through
the chosen open adjoints and tower functor objects. The new node records the
ordinary identification as a separate mathematical obligation, with a complete
proof plan in its docstring. It is a strictly lower ordinary normalization result, not the
derived theorem under another name.

## New nodes

`lem-sf-semilinear-scalar-ordinary-alpha-normalization`, in
`dag/nodes/sec-six-functors/`, states equality of the package's ordinary alpha
with canonical towerAlpha. Its module is
`Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryAlphaNormalization`.
The proof follows the source's intrinsic proper/open word and uses the already
stated ordinary comparison and ordinary strict-tower arrow nodes. Edge cases
include noncartesian squares, empty opens, and arbitrary coefficient rings;
none adds a hypothesis. No change record is needed because existing definitions
and statements are unchanged.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
