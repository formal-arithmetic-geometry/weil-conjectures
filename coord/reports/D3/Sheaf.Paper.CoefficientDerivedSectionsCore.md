## What changed

Added two proof-only imports and assembled `WeilConjectures.coefficientDerivedSectionsCore`
from two strictly smaller interfaces. `CoefficientDerivedSectionsCoreData` contains the
scalar coherence, finite evaluation comparisons and total-limit comparison. The equations
interface supplies the resolution equation and the finite projection equation. The item
proof is a real structure construction and transports the extracted resolution predicate
by definitional simplification.

## Proved and sorry left

The item theorem `WeilConjectures.coefficientDerivedSectionsCore` is proved. Two strictly
simpler split obligations remain, each with one `sorry`:

- `WeilConjectures.coefficientDerivedSectionsCoreData`, node
  `lem-coef-derived-sections-core-data`;
- `WeilConjectures.coefficientDerivedSectionsCoreEquations`, node
  `lem-coef-derived-sections-core-equations`.

No definition contains `sorry`.

## No longer needed

The direct generic comparison declarations remain used as proof dependencies of the two
split interfaces. No declared dependency was removed.

## Where the brief, the DAG or earlier work was wrong

The generic sections and sections-limit theorems operate on strict semilinear systems,
whereas this item records their transport to the coefficient sequence-site category.
Their package types therefore cannot be applied directly to the item. The construction
naturally separates into transported data and the two equations; the item proof now
records that assembly explicitly.

## New nodes

`lem-coef-derived-sections-core-data` records the transported scalar/evaluation/limit
interface. `lem-coef-derived-sections-core-equations` records the resolution and finite
projection equations for that interface.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CoefficientDerivedSectionsCore": "ffff8012a1456bc980d58a81c32816f379d3b562", "Sheaf.Paper.CoefficientDerivedSectionsCoreData": "208195ff1badddf61d11f55bce32a5dd8da3527e", "Sheaf.Paper.CoefficientDerivedSectionsCoreEquations": "924c6e50dae31f441617dfeac7e3e0779a3b9b73"}, "results": {}, "time": "2026-10-28T09:42:37+0800", "transitive": 0, "version": 1}
```

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
