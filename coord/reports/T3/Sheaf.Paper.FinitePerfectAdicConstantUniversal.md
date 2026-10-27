## What changed

Closed `AlgebraicGeometry.Scheme.finitePerfectAdicEtaleConstant_universal` by composing two strictly simpler transport statements. Added the proof-only imports and two split-off theorem modules.

## Proved and sorry left

The item theorem `finitePerfectAdicEtaleConstant_universal` is proved. Two strictly simpler intermediate theorems remain as named `sorry`s: `etaleNormalizationArrow_universal_of_constant` and `finitePerfectAdicLiftedTransition_universal`.

## No longer needed

The original planned dependencies `lem-weil-pbc-derived-scalar-extension-local-systems` and `lem-weil-pbc-constant-derived-normalization-universal` are not used directly by this proof; the generic source transport and lifted algebraic universality statements isolate those arguments.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled algebraic transpose universality, constant realization, and etale source transport into one step. The available declarations do not expose the required lifted transpose and source transport proof as finished lemmas, so these are split into two strictly simpler statements.

## New nodes

`lem-weil-pbc-finite-perfect-adic-lifted-transition-universal` records universality of the lifted algebraic transition. `lem-weil-pbc-etale-constant-arrow-universal-transport` records transport of a universal constant arrow to an etale source. Both node files and their modules are included in this delivery.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleNormalizationArrowUniversal": "2d6d404f5af17e0ed8d887770dc6807c966d32cd", "Sheaf.Paper.FinitePerfectAdicConstantUniversal": "919f654cf2f2ecd095e2d6694aa0f8ba1911dd1d", "Sheaf.Paper.FinitePerfectAdicLiftedTransitionUniversal": "1e4590e81e4928c33e2b63e87937b08ea64642b0"}, "results": {}, "time": "2026-10-28T04:19:56+0800", "transitive": 0, "version": 1}
```

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
