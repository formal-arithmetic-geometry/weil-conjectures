## What changed

Copied `Sheaf.Paper.FiniteFreeScalarDerivedComparison` into the sandbox and closed the
`derivedAssertions_of_finite_integral_resolution` hole by combining two strictly smaller
named interfaces: `finiteFreeScalarDerivedComparison_flatness` and
`finiteFreeScalarDerivedComparison_beta`. The independent projection theorem remains
open. Added DAG nodes and modules for the two split obligations.

## Proved and sorry left

Closed one original hole:

- `derivedAssertions_of_finite_integral_resolution`, by conjunction of the two split
  interfaces.

One original hole remains:

- `finiteFreeScalarProjection` (`sorry`), the finite-free cone projection isomorphism.

Two strictly smaller split obligations remain as named theorems with `sorry`:

- `finiteFreeScalarDerivedComparison_flatness` (`lem-sfb-finite-free-scalar-derived-comparison-flatness`).
- `finiteFreeScalarDerivedComparison_beta` (`lem-sfb-finite-free-scalar-derived-comparison-beta`).

No definitions contain `sorry`.

## No longer needed

The original monolithic proof dependencies are no longer attached directly to the item
proof; they are retained on the two split nodes, where their respective flatness and
normalized-beta roles are recorded. No imports were removed from the item module.

## Where the brief, the DAG or earlier work was wrong

The original proof bundled the independent K-flat/augmentation construction with the
normalized beta, pullback, and mate calculation. The Lean interface permits these as two
strictly smaller conjunction components, so the parent can be assembled by a real proof.
The projection argument is a separate cone exactness step and remains unresolved.

## New nodes

- `lem-sfb-finite-free-scalar-derived-comparison-flatness`
- `lem-sfb-finite-free-scalar-derived-comparison-beta`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteFreeScalarDerivedComparison": "0b2a490d4afa8f39e411fa45cd6b47ff522d4241", "Sheaf.Paper.FiniteFreeScalarDerivedComparisonBeta": "b71fadbf72b2a58bd5c4b4cadad994a2ca98a2b4", "Sheaf.Paper.FiniteFreeScalarDerivedComparisonFlatness": "9e71fc9c1a6ed6c7ee1d6ae0973a1e8fa3eb67ad"}, "results": {}, "time": "2026-10-28T06:28:16+0800", "transitive": 0, "version": 1}
```

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
