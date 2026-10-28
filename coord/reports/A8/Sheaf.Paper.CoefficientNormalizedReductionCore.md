## What changed

Added two independent statement modules splitting the core construction into (1) existence of the reduction record with the prescribed tensor record and (2) existence of the finite quotient calculus. The item theorem combines them and transports the calculus along the tensor equality.

## Proved and sorry left

The assembly theorem `coefficientNormalizedReductionCore` is proved. Two strictly smaller construction obligations remain as named sorries: `coefficientNormalizedReductionModel_exists` and `coefficientFiniteQuotientCalculus_exists`, with DAG nodes `lem-coef-normalized-reduction-model-existence` and `lem-coef-finite-quotient-calculus-existence`.

## No longer needed

No imports from the original item were removed. The proof uses only the evaluation-data interface and the two new split modules; the lower sequence-projection and scalar-pair modules remain stated dependencies of the split nodes.

## Where the brief, the DAG or earlier work was wrong

The direct construction planned by the DAG is substantial and is not already assembled in the imported evaluation-data module. The independent reduction and quotient constructions are genuine conjunctive components, so they were split into separate statement modules and combined by a real equality transport.

## New nodes

`lem-coef-normalized-reduction-model-existence` and `lem-coef-finite-quotient-calculus-existence` are the two strictly simpler construction obligations described above.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CoefficientFiniteQuotientCalculusExistence": "06dbd72fdc5ae59149d97ab370be4d166f80923e", "Sheaf.Paper.CoefficientNormalizedReductionCore": "195a26bc67cd72867e970be8a7869999b1be2ae7", "Sheaf.Paper.CoefficientNormalizedReductionModelExistence": "70029769f48ab23cf81ee3f32bce8912536a5b08"}, "results": {}, "time": "2026-10-28T07:56:13+0800", "transitive": 0, "version": 1}
```

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
