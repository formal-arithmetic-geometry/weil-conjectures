## What changed

The item module now imports three proof-only helper modules and proves
`openQuotientScalarUnitCompatibility` by composing their strictly smaller statements:
normalized scalar compatibility data, existence of the strict scalar comparison, and the
scalar-unit equation for fixed data. The existing definitions and the three already proved
unit-tower declarations are unchanged.

## Proved and sorry left

The item theorem `WeilConjectures.OpenTensorQuotient.openQuotientScalarUnitCompatibility`
is reduced to the three named helper theorems below. The helper theorem proofs remain
`sorry`, each with its own node and source docstring:

- `openQuotientScalarCompatibilityData` (`lem-sf-open-quotient-scalar-compatibility-data`);
- `openQuotientScalarComparisonExistence` (`lem-sf-open-quotient-scalar-comparison-existence`);
- `openQuotientScalarUnitEquation` (`lem-sf-open-quotient-scalar-unit-equation`) in the item module.

The unit equation theorem is a named public theorem in the item module; no definition contains `sorry`.

## No longer needed

The proof does not use `lem-sf-cbc-slice-tensor-generator-coherence`; it is removed from
the item's proof dependencies. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The prior delivery left the item theorem as a bare `sorry` and attempted a larger assembly
inside the item. The argument naturally separates into the three strict subclaims above;
the item now contains a real Lean composition of those subclaims. No target statement is
changed.

## New nodes

`lem-sf-open-quotient-scalar-compatibility-data` states existence of the finite and strict
system compatibility object. `lem-sf-open-quotient-scalar-comparison-existence` states the
strict comparison construction after that object and `tc` are supplied.
`lem-sf-open-quotient-scalar-unit-equation` states the remaining generator calculation for
fixed `sc` and `r`. Each is strictly weaker than the item conclusion. No change record is
needed because only new modules and proof dependencies are added.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenQuotientScalarComparisonExistence": "ed678ddd3345cec4e38c0ac85dc8f6d5441c987c", "Sheaf.SixFunctors.OpenQuotientScalarCompatibilityData": "a5b8f8c4087f16bdf8077f16e6f26b376d89a253", "Sheaf.SixFunctors.OpenTensorQuotientScalarCompatibility": "73304be7daa31ab1776826c5e62769021554a90b"}, "results": {"Sheaf.SixFunctors.OpenTensorQuotientCochains": {"hash": "87ce5d0d62cc2097a2fb8d472226a6c55794d836", "status": "OK"}}, "seconds": 127, "time": "2026-10-28T00:53:18+0800", "transitive": 0, "version": 1}
```

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
