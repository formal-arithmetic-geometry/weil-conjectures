## What changed

The assigned theorem now assembles a normalized coefficient-sections package from two
strictly smaller obligations.  `CoefficientDerivedSectionsCore` packages scalar
coherence, derived tower-section evaluation, the total-limit comparison and its
projection equation.  `coefficientDerivedSectionsScalarHomZero` isolates the final
degree-zero scalar Hom normalization.  The item theorem constructs the requested
structure and transports the core resolution equation definitionally.

The two helper modules and their DAG nodes are included in this delivery.  The item
module imports both helpers as proof-only imports.

## Proved and sorry left

The original theorem `coefficientDerivedSectionsNormalization` is proved by real
structure construction.  The two strictly simpler extracted obligations remain as
named `sorry` theorems:

- `coefficientDerivedSectionsCore`, node
  `lem-coef-derived-sections-normalization-core`;
- `coefficientDerivedSectionsScalarHomZero`, node
  `lem-coef-derived-sections-normalization-scalar-hom-zero`.

The delivery therefore closes one upper hole and adds two lower split holes as a
decomposition.  No definition contains `sorry`.

## No longer needed

No imports or declared proof dependencies were removed.  The generic section and
limit comparison declarations remain the proof dependencies recorded by the new
core node; the scalar Hom comparison declarations remain the dependencies of the
H-zero node.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan describes a long construction but does not expose a
single Lean theorem that performs it.  The existing generic comparison theorems
have substantially different package types, so the full construction cannot be
closed by a short direct application.  The obligation was decomposed into the core
package and its independent H-zero normalization, each strictly smaller than the
requested structure.

## New nodes

`lem-coef-derived-sections-normalization-core` records the core package and its
construction source.

`lem-coef-derived-sections-normalization-scalar-hom-zero` records the H-zero scalar
transpose calculation and its source.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CoefficientDerivedSectionsCore": "82dd514d8077fbffed24e583ae6295d2df56ced1", "Sheaf.Paper.CoefficientDerivedSectionsNormalization": "f970bc0c18e5e2aa468c47ae0e0a3f4e0a6aedf1", "Sheaf.Paper.CoefficientDerivedSectionsScalarHomZero": "d00f2e56d87dfa00affe041fee4cdd248ac71ef1"}, "results": {}, "time": "2026-10-28T05:18:25+0800", "transitive": 0, "version": 1}
```

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
