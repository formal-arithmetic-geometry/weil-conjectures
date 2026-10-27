## What changed

Restored the quarantined item source and implemented the actual adjunction-unit route.
Sequence pullback transitions follow from unit naturality. The inverse mate of direct-image
evaluation supplies the finite pullback models. Exact finite coefficient pullback and the
universal left-derived-functor property supply the computation comparison on every complex.
The scalar comparison uses the actual coefficient-ring square and uniqueness of left adjoints.
The final equation is checked degreewise after the two ordinary adjunction Hom bijections.
The scalar comparison lives in `Sheaf.Paper.StrictScalarPullbackComparison`; evaluation and
exactness live in `Sheaf.Paper.StrictPullbackEvaluationConstructor`. Both new helpers contain
complete proofs. The constructor imports the already-proved ordinary-adjunct and transition
section calculations from `StrictTensorOrdinaryAdjunct`. This reuse and separation keep the
individual files within the compilation bound. All three modules compiled successfully
through `lcompile.py`; the final constructor compile completed within the 60-second bound.
No shared definition, existing public signature, public import, or target statement is changed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.StrictQuotient.strictPullbackAdjointConstructor`.
Added zero holes. The two new public helper theorems
`WeilConjectures.StrictQuotient.strictScalarPullbackComparison` and
`WeilConjectures.StrictQuotient.strictPullbackEvaluationConstructor` are proved.
Every private helper is proved. No `sorry` remains in any delivered module.

## No longer needed

The proof does not invoke `lem-pur-quotient-operation-adjoint-factorizations`
(`Sheaf.Paper.QuotientOperationAdjointFactorizations`): its extra flatness hypotheses are
unnecessary for the actual finite geometric pullback.
It does not directly invoke `prop-weil-pbc-proetale-constant-ring-map` or
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: restriction and inverse image are
compared by their right adjoints and actual units instead of a derived tensor formula.
It uses the packaged `lem-pur-coefficient-pullback-exact` instead of a direct invocation of
`prop-weil-pbc-proetale-constant-exact`.
These entries are removed only from this node's direct proof dependencies; existing modules
and dependencies of imported declarations remain in the library. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item was quarantined, so its source was restored from the quarantine path specified by
`coord/rework.tsv`. Its absence from the Lean source root did not authorize withdrawal.
The planned generic factorization theorem is unnecessary: this statement quantifies over
all complexes, and exact finite coefficient pullback computes its derived functor without
assuming a flat complex. The new proof preserves the original statement and unit formulas.

## New nodes

`lem-pur-strict-scalar-pullback-comparison`, in
`dag/nodes/sec-smooth-purity/lem-pur-strict-scalar-pullback-comparison.json`, records
`WeilConjectures.StrictQuotient.strictScalarPullbackComparison` in the new module
`Sheaf.Paper.StrictScalarPullbackComparison`. This is the scalar-comparison step of
the original constructor argument, proved using composed right adjoints and their
ordinary unit identities. It has no `sorry`. The constructor reuses the existing ordinary-adjunct and transition
section calculations from `StrictTensorOrdinaryAdjunct` rather than duplicating their proofs.
There is no change record: only the assigned module, its own node, and the two new
proved helper modules and their nodes are changed.

`lem-pur-strict-pullback-evaluation-constructor`, in
`dag/nodes/sec-smooth-purity/lem-pur-strict-pullback-evaluation-constructor.json`, records
`WeilConjectures.StrictQuotient.strictPullbackEvaluationConstructor` in the new module
`Sheaf.Paper.StrictPullbackEvaluationConstructor`. It proves horizontal naturality,
evaluation by the actual finite inverse image, and the exact left-derived computation
comparison. The explicit inverse-mate construction also supplies the evaluation
isomorphism used by the constructor's final equation. It has no `sorry`.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
