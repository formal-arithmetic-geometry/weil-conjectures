## What changed

Replaced the hole in `WeilConjectures.integralObjectPullbackQuotientBasis` by a
proof from a normalized basis at each individual finite quotient exponent.
The new module `Sheaf.Paper.IntegralObjectFiniteBasis` constructs the generator
explicitly: take the inverse integral basis at a slice object, tensor its
section with one, apply the specified pullback adjunction unit, and restrict
along the distinguished map into the fibre product. Its remaining theorem
asserts that this generator gives a finite basis, with an explicit formula
for the inverse on every section.

The item module proves that the actual transition is the finite-linear mate
used in its construction, that it carries the displayed generator to the next
one, and that it carries `z` times that generator to the reduction of `z`
times the next generator. It then compares the two towers using the already
proved finite regular scalar multiplication isomorphisms and their transition
formula. Cancellation reduces the successor square to degree zero; all other
degrees of the regular single complex are zero.

Proof imports added: the new finite-basis module, the private construction API
of `IntegralOperationsWellDefined`, and the proved finite-multiplication part
of `ConstantScalarStrictUnit`. The original public import and original theorem
signature are preserved. No existing statement or definition is changed.

The proof gives the finite degree map an explicit module type, then forgets it
to a morphism of additive presheaves. Naturality and the scalar-action formula
are proved through this interface. The generator uses the underlying additive
presheaf restriction map. This preserves the actual sectionwise construction
and avoids repeated comparisons between different scalar-module structures.
The chosen transition is accessed through its specification.

Validation: both modules compiled with the required server `lcompile.py`.
The parent compiled in 48.9 seconds with diagnostics enabled (kernel checks
about three seconds); the finite-basis module compiled in 6.3 seconds.
The final packet removes diagnostics, profiling, boundary markers and temporary
heartbeat settings. Delivery recompiles this cleaned packet.

## Proved and sorry left

Original hole closed:
`WeilConjectures.integralObjectPullbackQuotientBasis`
(node `lem-pur-integral-object-pullback-quotient-basis`).

One hole added and left:
`WeilConjectures.IntegralObjectQuotient.finiteNormalizedBasis`
(node `lem-pur-integral-object-finite-basis`). It concerns a single exponent,
before restriction to the completed coefficient ring, and states the inverse
on sections. It asserts no transition equation. The construction of its
generator is explicit and contains no hole. The inverse formula uniquely
determines the isomorphism: degree zero is determined on every section, and
all other degrees are zero. No arbitrary object is defined by selecting a
witness from this theorem.

This is a decomposition: one original hole closed and one strictly smaller
hole added in these two modules. No net closure gain is claimed; project-wide
figures are determined by the ledger. The transition compatibility and the
comparison with the scalar tower are proved in Lean; the finite-level
localization construction remains. The existing localization and normalized
object inverse-image comparison statements are the dependencies of that
remaining construction, rather than new restatements of them.

Edge cases checked mathematically: the formula uses no flatness and no
invertibility of the prime on the scheme. In a zero coefficient ring the
regular module and the generator are zero. On the empty scheme the same
sheaf and adjunction constructions apply. No argument requires a nonzero
section or a nonempty site object.

## No longer needed

No module or node is globally pruned, and no existing import is removed.
The parent's direct uses of
`lem-pur-ringed-site-pullback-localization-universes` and
`lem-sfb-proetale-object-inverse-image-restriction` are now carried by the
finite-basis node; both remain necessary there. The existing strict regular
scalar unit node remains necessary through its finite multiplication theorem.
There is no bypass of a unit statement or a unit proof step.

## Where the brief, the DAG or earlier work was wrong

The earlier plan grouped finite-level localization and the transition
calculation into one obligation. Its mathematical argument is retained, but
its Lean interfaces do not directly provide the normalized finite basis.
The new node isolates this construction. The transition part is proved using
its inverse formula, without assuming a compatible family of bases.

The full regular scalar unit theorem carries an irrelevant finite-field
datum. Its already proved finite-multiplication component has no such
hypothesis and is available through a private proof import, so no datum is
introduced and no existing statement is changed.

## New nodes

`lem-pur-integral-object-finite-basis`, in
`dag/nodes/sec-smooth-purity/lem-pur-integral-object-finite-basis.json`, records
the normalized finite-level construction, its localization and object
restriction dependencies, the explicit inverse formula, the proof in words,
and searches with LeanSearch, LeanFinder, Loogle, and source grep. Its module
is `Sheaf.Paper.IntegralObjectFiniteBasis`. It is strictly a construction step
of the old argument: it neither compares the two strict towers nor states
any successor square. The parent node's proof and proof dependencies now
follow the delivered combination of this step with the proved transition
and scalar-normalization calculations.

No change record is required: all existing declarations keep their signatures
and definitions; the delivery adds one new statement module and changes the
item's proof and proof dependencies.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
