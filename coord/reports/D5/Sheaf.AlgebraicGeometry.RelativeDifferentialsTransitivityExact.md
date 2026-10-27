## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.Hom.relativeDifferentials_transitivity_exact`
without changing its signature or public imports. The canonical second arrow is constructed
from the universal property of relative differentials. Injectivity of the tensor-adjunction
and differential Hom equivalences proves that the composite vanishes. The module-stalk
criterion gives middle exactness, and the section formula directly proves epimorphicity.
On source opens an isomorphism of short complexes transports exactness and epimorphicity
across the associativity congruence.

Added `Sheaf.AlgebraicGeometry.RelativeDifferentialsTransitivityAffineStalk`, which states
the remaining normalized affine-comparison and localized-exactness step, and
`Sheaf.AlgebraicGeometry.RelativeDifferentialsTransitivityOpen`, which proves the source-open
comparison by the tensor and restriction adjunctions. The latter constructs its own canonical
second arrow, proves both commuting squares, and normalizes the first comparison on actual
pulled-back differential sections. Updated the parent DAG proof to match the Lean assembly.

Remote `lcompile.py --all` passed for all three files, respectively in 5.3, 20.5,
and 16.6 seconds, without errors or warnings. The original theorem signature is
byte-identical; both new node attachments match their Lean signatures, and each
node's proof dependency list is exactly the union of its proof-step uses.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials_transitivity_exact` is closed by a complete
Lean proof from the new intermediate theorem. The added theorem
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials_transitivity_open`
(node `lem-a1-differential-transitivity-open`) is proved and has no holes.

One new hole remains:
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials_transitivity_affine_stalk`
(node `lem-a1-differential-transitivity-affine-stalk`). Its entire proof is `by sorry`;
its docstring and node contain the affine comparison, generator, and localization argument.
It asserts only the affine/stalk step for a supplied normalized quotient map, not existence
of that map, sheaf exactness, or the source-open comparison. The parent constructs the map
and proves those additional steps in Lean.

Holes closed: 1. Holes added: 1. Holes left in the item: 0. This is a decomposition with
net hole change zero, not a proof independent of the remaining affine/stalk theorem.

## No longer needed

Removed the item's private imports `WeilConjectures.AlgebraicGeometry.TensorPullbackTilde`
and `Mathlib.RingTheory.Etale.Kaehler`: its proof now uses the named affine/stalk step instead
of performing the algebraic calculations inline. Those calculations and every original
mathematical dependency remain in the new affine/stalk node's proof plan. No existing node
or module is withdrawn or claimed to be globally unnecessary. No unit route is bypassed.

The plan's gluing construction of the second arrow is unnecessary: the universal property
constructs it directly on the whole scheme. Neither new statement introduces any smoothness,
flatness, finite-type, or nonemptiness hypothesis.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was required. The original plan is mathematically valid,
but the universal property avoids its gluing step. The epimorphism also follows directly
from the generator formula and universal property, without another application of the
stalk criterion. The fixed source-open associativity congruence must be retained; the proof
handles it by equality induction and a short-complex isomorphism.

## New nodes

`lem-a1-differential-transitivity-affine-stalk` records steps 1–3 of the old plan as one
strictly partial intermediate statement: the normalized affine charts and localized
exactness for an already supplied quotient map. Its sole theorem remains sorry.

`lem-a1-differential-transitivity-open` records only the normalized source-open comparisons
and the local second arrow's generator formula. It does not assert exactness; the item
proves source-open exactness separately by applying the affine/stalk statement and
transporting a short complex. Its theorem is proved using adjunctions and universal
properties. Both nodes inherit the item's chapter, unit, source, and blueprint ancestry.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
