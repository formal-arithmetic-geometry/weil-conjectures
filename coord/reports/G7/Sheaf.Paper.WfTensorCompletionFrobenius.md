## What changed

In `Sheaf.Paper.WfTensorCompletionFrobenius`, proved
`WeilConjectures.wfTensorCompletionFrobenius_unique` and
`WeilConjectures.wfTensorCompletionCommonField` without changing their statements.
A proved private helper shows that normalization alone identifies comparison packages:
precomposition with the integral localization determines each rational bifunctor,
and the prescribed integral components determine all three natural isomorphisms.
The proof reuses `scalarLocalization_precomp_injective` from `WeilTensorProduct`
through an additional private `import all`; currying applies it in both variables.
The common-field theorem specializes the existing existence theorem at G, identifies
its normalized package with the given R, and maps the resulting Weil isomorphism
through the common-stage inclusion. No integral lifts of rational Weil structures
are assumed.

Updated the owning nodes to describe these proofs and expanded the existing
existence obligation's docstring and node into its scalar-extension construction.
All declarations, definition bodies and public imports retain their interfaces.

## Proved and sorry left

Closed two of the three original holes:

- `WeilConjectures.wfTensorCompletionFrobenius_unique`
  (`lem-wf-tensor-completion-frobenius-uniqueness`).
- `WeilConjectures.wfTensorCompletionCommonField`
  (`lem-wf-tensor-completion-frobenius`).

One existing hole remains:

- `WeilConjectures.wfTensorCompletionFrobenius_exists`
  (`lem-wf-tensor-completion-frobenius-existence`). Its proof is exactly `by sorry`;
  its docstring now details the bilinear Hom extension, natural comparison maps,
  rational Weil equation and induced IsoAlgebra isomorphism.

Added zero holes and zero split statements. The main existence-and-uniqueness
theorem retains its complete assembly proof and still depends on this existence
obligation. The common-field proof also depends on that named obligation.

## No longer needed

No modules, imports or nodes are withdrawn. The uniqueness argument needs only
normalization; its additional FullProperty equations and Weil-pair witnesses are
unused. A separate common-field descent obligation is unnecessary: functoriality
of the existing common-stage inclusion supplies the final image isomorphism.
The declared constructible-unit and pullback-unit-square dependencies remain in
use by the integral results and the remaining existence construction.

## Where the brief, the DAG or earlier work was wrong

The existing uniqueness node's proof said only that the argument was deferred.
It is now a complete proof using raw localization and component normalization.
The existing existence node had the same placeholder text; it now records the
actual construction still to formalize, without introducing another copy of its
statement. Normalization alone is sufficient to compare packages, so the given
common-field hypothesis does not need to assert the full Weil equation.

The current server queue lists a stage-3 proof item with three holes. The archived
build error is a bad import of WfConstructibleTensorKoszulUnit; the unchanged item
compiled against the current published artifacts in 26.1 seconds. No dependency
archive, source declaration or Lean attachment was removed to evade that error.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 3 OK, 1 SLOW.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.Paper.WfTensorCompletionFrobenius": "686c411f5e4981bf6ae2d08da4996cf58d8fd7f4"}, "results": {"Sheaf.Paper.CompactSupportProjectionFormula": {"hash": "9d8a08bf4a6d4025a7ffc9ce8b51e70bcc8ad44a", "status": "OK"}, "Sheaf.Paper.ProjectionRationalTensorDescent": {"hash": "bc5e701300fee22ec664dd58eeb82f7145f0a2c3", "status": "OK"}, "Sheaf.Paper.ProjectionTensorCoefficientComparison": {"hash": "1b3f917c718a23cd0c8025ed4ef15d7d7f6e6f1c", "status": "OK"}, "Sheaf.Paper.ProjectionWeilTensorDomainBridge": {"hash": "ff2e4ac76a3581b5777f72de17fb80ec5a21c6b9", "status": "SLOW"}}, "seconds": 251, "time": "2026-10-28T00:36:23+0800", "transitive": 0, "version": 1}
```

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
