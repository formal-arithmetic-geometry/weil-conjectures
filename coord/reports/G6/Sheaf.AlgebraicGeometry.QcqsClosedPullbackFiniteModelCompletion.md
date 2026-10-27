## What changed

Filled `AlgebraicGeometry.ProEtale.QcqsClosedPullback.derived_completion` in
`Sheaf.AlgebraicGeometry.QcqsClosedPullbackFiniteModelCompletion` without changing
its statement or any definitions. Extract the K-flat representative from completeness,
apply `normalized_strict_completion` to this representative, and use its K-flatness
and completion-unit equation. The source completion map is invertible because it
is the composite of the representative inverse and its invertible augmentation.
Its image followed by the normalized comparison is invertible, so
`AdicCompletion.isDerivedComplete_iff` proves completeness of the pulled-back object.
This is exactly step 6 of the existing node; the proof route and unit route are unchanged.
No modules outside the item are changed, no imports are added, and no new nodes are needed.

## Proved and sorry left

Closed one of the three original direct holes:
`AlgebraicGeometry.ProEtale.QcqsClosedPullback.derived_completion`.
This is a complete Lean deduction from the existing normalized strict-comparison
theorem and representative criterion; it still transitively depends on the former.
No holes are added or split off.

Two original named holes remain unchanged, both attached to
`lem-sfb-qcqs-closed-pullback-finite-model-completion`:

- `AlgebraicGeometry.ProEtale.QcqsClosedPullback.finite_models_constructible_tor`.
- `AlgebraicGeometry.ProEtale.QcqsClosedPullback.normalized_strict_completion`.

Validation: single-file compilation through `lcompile.py`, followed by the delivery
checks and axiom/sorry probe through `deliver3.py`.

## No longer needed

None. The two unfinished theorems retain their existing proof dependencies and imports.
The proved consequence uses the existing strict comparison, so no node or module is
made unnecessary by this delivery. No public imports or declarations are removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The final consequence needs neither a new
K-flat resolution nor an independent representative-invariance argument: the input
completeness predicate already supplies a representative, and the two existing
comparison APIs give the exact normalized unit and the target completeness criterion.
The finite-model and strict-coordinate assembly remain separate unfinished work.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
