## What changed

Proved `Algebra.irreducibleSpace_tensorProduct_iff_finite_separable` in
`Sheaf.AlgebraicGeometry.GeometricIrreducibilityFiniteSeparableTest`, preserving its
signature and all public imports. Three proved private helpers implement descent of
irreducibility along injective ring maps, simultaneous descent of two tensor elements
to a finite separable coefficient field, and the separable-closure test.

The reverse implication first transports finite tests across `ULift`, then proves
primality of the nilradical after the separable closure. A common extension of that
closure and the arbitrary test field allows application of the existing separably
closed tensor-irreducibility theorem. Tensor reassociation and injective descent
finish the argument. No definition or public interface changed, and no consumer
adaptation is needed. The existing DAG node now records these implementation details.

Added proof imports for finite coefficient support, finite integral algebras, lifted
fields, and faithful-flat tensor nontriviality. The file compiles cleanly through
`lcompile.py` (4.5 seconds at the last proof check).

## Proved and sorry left

Closed 1 of 1 original holes:
`Algebra.irreducibleSpace_tensorProduct_iff_finite_separable`
(node `lem-zl-geometric-irreducibility-finite-separable-test`).

Holes added: 0. Holes left in the delivered module: 0. Split-off statements: 0.
All three private helpers are proved. This is a proof from existing declared
inputs: the imported `IsSepClosed.irreducibleSpace_tensorProduct` remains the
existing next item (node `lem-zl-sepclosed-algebras-tensor-irreducible`); this
delivery neither adds nor modifies that hole.

## No longer needed

Removed the proof import `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra` and the
proof dependency `lem-weil-pbc-faithfully-flat-ideal-contraction`. Direct field-linear
flatness gives all needed tensor-map injections, so contraction of extended ideals
is unnecessary. `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` supplies tensor
nontriviality instead.

Removed `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`: the proof only needs
Mathlib's `SeparableClosure`, its instances, and algebraicity of its subalgebras,
not the source module's additional declarations. It imports
`Mathlib.FieldTheory.IsSepClosed` directly. The node `def-pd-separable-closure`
remains needed for the separable-closure construction. All other declared proof
dependencies remain used. No Lean module is withdrawn; no unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The planned faithful-flat ideal-contraction
argument was longer than necessary in Lean: field-linear flatness already proves
the required injections. The finite coefficient passage is implemented using the
supremum of two finitely generated subalgebras and the canonical intermediate field
of an algebraic subalgebra. The large-universe quantifier also requires explicit
`ULift` transport before applying the test at the base field and its finite
subextensions. The zero-ring case is excluded by nonemptiness of the finite test
at the base field; reducedness and finite generation of the original algebra are
never assumed.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
