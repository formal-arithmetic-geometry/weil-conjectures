## What changed

Proved `Algebra.normal_tensorProduct_of_isSeparableExtension` in
`Sheaf.FieldTheory.SeparableFieldGeometricallyNormal` with its signature unchanged.
Four proved private helpers implement the existing five-step DAG plan:

- Reduce tensor reducedness to finitely generated subalgebras, embed each in its
  finitely generated intermediate field, and apply
  `Algebra.isReduced_tensorProduct_of_isSeparablyGenerated`.
- Use Mathlib's purely inseparable tensor power lemma and reducedness to prove
  every nonzero tensor is a unit, giving a field.
- Transport normality through the induced prime-localization equivalences.
- Prove prime-localization normality for fields.

The main proof takes the relative perfect closure in `AlgebraicClosure k`, applies
`Algebra.normal_tensor_perfectClosure_iff`, and transports through tensor swaps
and a universe lift. The existing node's route and dependencies are retained;
these are elementary implementations of its steps, with no new public statements.
Added proof imports for `Mathlib.Algebra.Field.ULift` and
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.

Validation: the complete module compiles through `lcompile.py` with no warnings.

## Proved and sorry left

Closed 1 of 1 original holes:
`Algebra.normal_tensorProduct_of_isSeparableExtension`
(node `lem-weil-pbc-separable-field-geometrically-normal`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
All four private helpers are proved. The theorem still uses the existing stated
`Algebra.normal_tensor_perfectClosure_iff` (node
`lem-weil-pbc-geometrically-normal-perfect-closure-criterion`), whose separate
module has its own existing hole; this delivery does not claim to close it.

## No longer needed

Removed `import Mathlib.RingTheory.RingHom.Flat`: the proof uses the module-flatness
API in `Mathlib.RingTheory.Flat.Basic` directly, without ring-hom flatness.
No DAG dependency or library module is pruned: all eight declared dependencies
are used as in the original plan. In particular the flat-ring-map definition node
also records `Module.Flat`, which is used for tensor injectivity.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The geometric-normality criterion quantifies over
fields in a common maximum universe, so the final proof explicitly lifts the
arbitrary field `E` and transports the conclusion back. No statement or definition
repair was needed.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
