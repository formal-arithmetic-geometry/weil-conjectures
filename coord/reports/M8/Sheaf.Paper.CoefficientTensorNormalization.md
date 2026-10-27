## What changed

The parent theorem now combines five named component theorems. Each component theorem is a
strictly smaller displayed equation and is left as a named proof obligation with its own DAG
node. The parent imports the five component modules and proves the conjunction by `refine ⟨...⟩`.

## Proved and sorry left

The parent declaration `coefficientTensor_normalization` is reduced to the five component
statements. Five strictly smaller named obligations remain, each with one `sorry`:

- `coefficientTensor_normalization_unit` (`lem-sf-coefficient-tensor-normalization-unit`)
- `coefficientTensor_normalization_tower` (`lem-sf-coefficient-tensor-normalization-tower`)
- `coefficientTensor_normalization_quotient` (`lem-sf-coefficient-tensor-normalization-quotient`)
- `coefficientTensor_normalization_finite` (`lem-sf-coefficient-tensor-normalization-finite`)
- `coefficientTensor_normalization_scalar` (`lem-sf-coefficient-tensor-normalization-scalar`)

Thus one parent sorry was closed by a genuine decomposition into five component sorries.

## No longer needed

No existing imports or declared proof dependencies were removed. The component route uses the
same coefficient calculus and scalar comparison modules as the parent statement.

## Where the brief, the DAG or earlier work was wrong

The parent proof plan requires five substantial normalization identities, but the repository
provided no declarations of those identities. The parent cannot be closed by generic `aesop` or
category simplification: the tensorators are stored as chosen comparison data, and the relevant
monoidal category instances are intentionally abstract. The decomposition records each missing
identity separately while preserving the exact parent statement.

## New nodes

The five component modules and their nodes listed under `## Proved and sorry left` are new.

Node ids: lem-sf-coefficient-tensor-normalization-unit, lem-sf-coefficient-tensor-normalization-tower, lem-sf-coefficient-tensor-normalization-quotient, lem-sf-coefficient-tensor-normalization-finite, lem-sf-coefficient-tensor-normalization-scalar.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.CoefficientTensorNormalization": "553a94bcc3e0ea81a587bea5a0092edd0cccb6c3", "Sheaf.Paper.CoefficientTensorNormalizationFinite": "08b05e9dc2a9993a0c05e7c217cf757882aa8451", "Sheaf.Paper.CoefficientTensorNormalizationQuotient": "4640922b738e7b69cd1cd92837db160e3e3bb820", "Sheaf.Paper.CoefficientTensorNormalizationScalar": "1583394d7fdd1480d97561e587555a30505f9782", "Sheaf.Paper.CoefficientTensorNormalizationTower": "552d963f5c5ac17b1cb280e564fb105d0b2d23bc", "Sheaf.Paper.CoefficientTensorNormalizationUnit": "5c4c33f4c15a76a084f9f64f21b87f8367455f52"}, "results": {"Sheaf.Paper.BasicOperationReductionAndEvaluation": {"hash": "b59908be23268f1bf8d538f6d35ec39a1f546105", "status": "OK"}, "Sheaf.Paper.GeneralHomComparisonCocycles": {"hash": "d868c7f7d9bcfda76be62f0fec6e271641b39e6e", "status": "OK"}}, "seconds": 66, "time": "2026-10-28T03:41:08+0800", "transitive": 0, "version": 1}
```

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
