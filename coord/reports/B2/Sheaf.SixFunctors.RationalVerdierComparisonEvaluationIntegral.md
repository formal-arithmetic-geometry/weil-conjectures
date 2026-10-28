## What changed

Replaced the sorry in `WeilConjectures.RationalVerdier.normalizedExtension_evaluation_integral`
by the integral adjunction calculation followed by explicit localization transports.
The statement and all its hypotheses are unchanged. The proof uses the existing
`IntegralFiniteExtension.v_evaluation`, counit naturality, completion naturality, and
`integralEvaluation`. The localization step retains the object equalities and the
heterogeneous equalities for tensor maps, evaluation and the tensorator inverse.

Added `Sheaf.SixFunctors.RationalVerdierTensorScalarCompletion` for the remaining
normalized tensor/completion square. Unlike the assigned statement, this square has no
internal Hom, dualizing datum, beta, evaluation, rational objects, or normalization
hypotheses about an Extension. It is used with the pair `(K, D K)`. Both modules keep
`backward.isDefEq.respectTransparency` enabled. No existing public interface changes. The assigned module compiles cleanly in 38.0 seconds;
the new module compiled in 19.0 seconds (its one declared sorry is expected).

## Proved and sorry left

One original hole closed by decomposition:
`WeilConjectures.RationalVerdier.normalizedExtension_evaluation_integral`
(node `lem-coef-rational-verdier-comparison-evaluation-integral`).

One new hole remains:
`WeilConjectures.RationalVerdier.tensor_scalar_completion`
(node `lem-coef-rational-verdier-tensor-scalar-completion`). Its docstring gives the
K-flat pure-tensor calculation and descent argument. The zero-object and identity
extension cases have the same quotient and zero-coordinate formulas. No definition
contains a sorry. Net hole reduction is zero; this is a decomposition, not a complete
proof of the normalized completion calculation.

## No longer needed

No imports or modules are pruned. The separate proof dependency
`def-sf-integral-hom-reduction-models` is not used by this route: ordinary evaluation
follows directly from the existing transpose calculation. It remains a statement
dependency and remains used elsewhere; no module is withdrawn. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original single proof step omitted the formal distinction between ordinary and
completed tensor scalar comparisons. Transposition alone proves the ordinary
evaluation equation. The normalized tensor/completion square is the remaining
separate calculation; the new node records exactly that part. No statement is disputed.

## New nodes

`lem-coef-rational-verdier-tensor-scalar-completion` states the inverse tensor/completion
square for arbitrary normalized ordinary tensor presentations and integral constructible
inputs. Its source is the ordinary-to-completed comparison in paragraph 3 of
`thm-coef-rational-verdier.proof.md`, together with the finite-free completion argument
of `lem-coef-integral-finite-extension.proof.md`. The parent node now records the actual
two-step argument. No change record is needed: only the assigned module, its node,
and the new module and node are changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierComparisonEvaluationIntegral": "8a567e9e18e95e57719dd681bc9062ed585c4222", "Sheaf.SixFunctors.RationalVerdierTensorScalarCompletion": "0ad0bb8e58546dee83377f5eedc726afd5661bad"}, "results": {"Sheaf.SixFunctors.RationalVerdierComparisonEvaluation": {"hash": "196e72a39aa1a5e37100add2794fbcdceb0566b2", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T10:50:35+0800", "transitive": 0, "version": 1}
```

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
