## What changed

Added two proof modules. `OpenQuotientScalarFiniteCompatibilityGenerator` introduces finite-level comparison data and leaves its construction as one named theorem. `OpenQuotientScalarFiniteCompatibilityAssembly` proves the categorical assembly with `NatIso.ofComponents`. The item theorem chooses the finite-level data and applies the assembly.

## Proved and sorry left

Proved `openQuotientScalarFiniteCompatibilityAssembly` and `openQuotientScalarFiniteCompatibility`. One sorry remains in `finiteScalarLevelData_exists`, a strictly simpler finite-level generator statement, recorded in node `lem-sf-open-quotient-scalar-finite-compatibility-generator`.

## No longer needed

No imports from the original item were removed. The direct generator calculation is isolated in the split-off theorem; no additional planned nodes were used.

## Where the brief, the DAG or earlier work was wrong

The original proof plan compresses the finite-level generator construction and the natural assembly into one statement. The assembly itself is elementary once the finite-level objectwise data and naturality are stated separately, so it is split into a proved assembly theorem and one remaining generator theorem.

## New nodes

`lem-sf-open-quotient-scalar-finite-compatibility-generator` records the finite-level objectwise comparison and naturality data. `lem-sf-open-quotient-scalar-finite-compatibility-assembly` records and proves its assembly into functor isomorphisms.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenQuotientScalarFiniteCompatibility": "53d80b83757cac66b8f9415b625ae6dbc52acdc2", "Sheaf.SixFunctors.OpenQuotientScalarFiniteCompatibilityAssembly": "028d8768199cb556801052d40a3fd65082914d10", "Sheaf.SixFunctors.OpenQuotientScalarFiniteCompatibilityGenerator": "e07ff3b045ca8b3fab253eec84ba0528070e95a0"}, "results": {}, "time": "2026-10-28T09:57:40+0800", "transitive": 0, "version": 1}
```

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
