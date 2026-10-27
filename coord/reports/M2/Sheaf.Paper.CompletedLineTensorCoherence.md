## What changed

In `Sheaf.Paper.CompletedLineTensorCoherence`, prove
`WeilConjectures.CompletedLineTensor.associatorData_existsUnique` without changing its
statement or any existing definition. The item adds only the proof import
`Sheaf.Paper.CompletedScalarAssociator`; its proof unfolds the package definitions
and uses the support theorem.

Three new modules contain fully proved support APIs. `CompletedScalarPresentation`
bundles the existing ordinary functor, derived functor and universal counit as a
successive-derived-quotient presentation, with explicit equations to the recorded
functors, sections and counit. `PrescribedScalarAssociator` applies the existing
proved generic normalized adjunction comparison to prescribed presentations and
proves ordinary uniqueness by the two extension-restriction adjunctions.
`CompletedScalarAssociator` proves composition of completed coefficient maps by
finite quotient projections and specializes that construction to the actual recorded
presentations. Its private representative formula holds on every unbounded cochain
complex. Its public API packages the unique associator pair on good complexes,
proving derived uniqueness by localization extensionality and cancellation of the
K-flat counit using the existing cochain-model computation API.

Explicit presentation fields, projection equations and a private comparison structure
avoid repeatedly unfolding nested existential choices and sheafification data.
The generic construction and the native specialization are separate modules after
these improvements, and the final termwise lift uses exactly the same cochain-functor
ascription as the existing definition. This removes the costly final conversions
from the large item file. No shared definition or instance is changed.

## Proved and sorry left

Closed one of the seven original holes:
`WeilConjectures.CompletedLineTensor.associatorData_existsUnique`
(node `lem-pur-completed-line-tensor-coherence`). Added zero holes and split off zero
proof obligations. All three new support theorems are fully proved. The following six original holes remain:

- `WeilConjectures.CompletedLineTensor.complete`
  (node `lem-pur-signed-line-legacy-completeness`).
- `WeilConjectures.CompletedLineTensor.pairData_existsUnique`
  (node `lem-pur-completed-line-tensor-coherence`).
- `WeilConjectures.CompletedLineTensor.beta_natural_evaluation`
  (node `lem-pur-completed-line-tensor-coherence`).
- `WeilConjectures.CompletedLineTensor.scalar_coherence`
  (node `lem-pur-completed-line-tensor-coherence`).
- `WeilConjectures.CompletedLineTensor.tower`
  (node `lem-pur-completed-line-tensor-coherence`).
- `WeilConjectures.CompletedLineTensor.canonical_restriction`
  (node `lem-pur-completed-line-tensor-coherence`).

Validation: the presentation module compiled in 43.9 seconds, the generic bridge
in 14.0 seconds, the completed specialization in 34.5 seconds, and the item in
48.8 seconds. `exists_unique` and `associatorData_existsUnique` both print only
`propext`, `Classical.choice`, and `Quot.sound`; neither depends on `sorryAx`.
The first delivery check measured an earlier item proof at 64.5 seconds and pushed
nothing. The final proof uses explicit package unfolding and direct application of
the fully proved support API. Temporary profiling and axiom-print commands were
removed. All Lean lines are at most 100 characters.

## No longer needed

None. No imports, modules, declarations or DAG dependencies are removed. The remaining
open clauses still require the existing planned dependencies. The new associator proof
uses the already declared successive-derived-quotient normalization dependency.

## Where the brief, the DAG or earlier work was wrong

The initial queue figure of eight holes was stale: the assigned source has seven,
and the refreshed queue now also records seven. `rational_diagonal` already has a
complete proof. No statement defect was found in the associator clause.
The generic public existence theorem chooses its own presentations, so applying it
alone would not normalize the recorded scalar functors. Instead the proof specializes
its existing proved construction to the exact choices already defining those functors.

The existing planned route for `complete` cites
`Sheaf.Paper.IntegralLineTensorCompleteness`, but that module imports this item and
proves its result using `CompletedLineTensor.complete` at signed power one. It cannot
be imported here to discharge `complete` without an import cycle. The remaining
completeness clause needs the actual reduction-tower transport argument; this delivery
does not change it or the cited source module.

## New nodes

`lem-pur-completed-scalar-presentation-exists` records
`WeilConjectures.CompletedScalarAssociator.presentation_exists` in
`Sheaf.Paper.CompletedScalarPresentation`. It packages the exact existing scalar
functors, tensor sections and universal counit, with no new completion model and no
new sorry. Mathlib searches found only ordinary module change of rings and unrelated
module-sheaf presentations.

`lem-pur-completed-scalar-associator-exists` records
`WeilConjectures.CompletedScalarAssociator.exists_unique` in
`Sheaf.Paper.CompletedScalarAssociator`. It supplies the unique ordinary and derived
associator pair with the exact tensor and good-complex representative formulas,
with no new sorry. Its construction uses the prescribed-presentation bridge; that bridge retains the
proved APIs of `SuccessiveDerivedQuotientNormalization` through a proof-only import. Mathlib searches found ordinary module associativity and
sheaf pullback associativity, which do not provide the prescribed counit comparison.

No change record is needed: no other existing module, statement or definition changes.

`lem-pur-prescribed-scalar-associator` records
`WeilConjectures.CompletedScalarAssociator.presentation_associator_exists` in
`Sheaf.Algebra.Homology.PrescribedScalarAssociator`. It proves the generic comparison
for a supplied family of presentations, including the supplied universal counits,
rather than choosing a different family. This is a proved bridge to the existing
normalization construction, with zero holes. Mathlib searches found tensor-product
and ordinary module-category associators, which do not provide the prescribed
module-sheaf universal-counit equation.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Algebra.Homology.PrescribedScalarAssociator": "edec8938a5033bbca570d9b7df2f5a34efed2e7c", "Sheaf.Paper.CompletedLineTensorCoherence": "5028ffea7dab73d033ffffdee5d74760b966d672", "Sheaf.Paper.CompletedScalarAssociator": "5f2af2af5d973944fb15c81eca14ede98a771000", "Sheaf.Paper.CompletedScalarPresentation": "98939bc72ead35a983a779e286ec6cda22f3a805"}, "results": {}, "time": "2026-10-28T04:41:29+0800", "transitive": 0, "version": 1}
```

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
