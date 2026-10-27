## What changed

Replaced the proof of `AlgebraicGeometry.exceptionalOriginAdjunctionEvaluation`.
The unit and counit equations follow from compatibility of the origin Hom
transposes with evaluation. This compatibility is proved by evaluating the
recorded transpose equations and cancelling the invertible source-site counit.
The quotient equation follows from the supplied etale quotient equation and the
site scalar-adjunction mate identities. All calculations take place in the
unbounded derived categories. No assertion is inferred from agreement at every
evaluation.

The original theorem statement and public import are unchanged. Added only
proved private calculation lemmas and a proof import of
`Sheaf.CategoryTheory.DerivedCategory.AdjunctionMateTranspose`. Local transparency
and instance settings keep the small interface wrappers accessible while leaving
derived localizations and mate constructions sealed. Updated the item's DAG
proof and proof dependencies to match this calculation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exceptionalOriginAdjunctionEvaluation` (all three conjuncts).
Added zero holes; zero holes remain in the delivered module. No intermediate
statement was split off.

Validation: the final file compiled without warnings in 46.1 seconds through
`lcompile.py`. The `#print axioms` audit of the theorem reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The theorem signature is textually identical
to the original, and every Lean line is at most 100 characters.

## No longer needed

Removed these planned proof dependencies from the item's DAG route:

- `lem-pur-coefficient-system-derived-comparison`: the comparison data are already
  supplied in `CX`, `CY`, and `CZ`; their existence need not be reproved.
- `lem-pur-etale-coefficient-system-adjoint`: `G` is already a supplied strict
  exceptional adjoint with evaluation and quotient equations.
- `lem-coef-semilinear-derived-sections`: no new scalar comparison is constructed.
- `lem-sfb-etale-proetale-scalar-pullback-cube`: the required scalar mate equations
  are fields of the supplied image data and are used directly.

No module is withdrawn. The public interface import still provides types used in
the statement; no public import was removed. Private calculation lemmas reproduce
only the generic mate identities needed here, without importing the unrelated
Brown-support transition module.

## Where the brief, the DAG or earlier work was wrong

The planned geometric existence dependencies are unnecessary for this conditional
interface theorem: its supplied records contain the precise evaluation and scalar
mate data. The proof uses `record.siteX.counit` to cancel the evaluated source
counit, so the separate finite-counit hypothesis is redundant for this argument;
it is retained verbatim.

The current queue assigns a proof task. The earlier missing-file build record
concerns an old quarantine; the current item source is present and its single
proof hole is the obligation addressed here.

## Related modules compiled before delivery

Not checked: the delivered modules did not compile in the overlay (service fault); the landing compiles the related modules.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalOriginAdjunctionEvaluation": "ad7c03d23aeb451664a48a637da9cbb090928e23"}, "own_failed": ["Sheaf.Paper.ExceptionalOriginAdjunctionEvaluation"], "results": {}, "time": "2026-10-28T01:16:34+0800", "transitive": 20, "version": 1}
```

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
