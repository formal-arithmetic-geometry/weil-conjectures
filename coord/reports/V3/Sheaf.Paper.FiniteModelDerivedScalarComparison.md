## What changed

Added two proof-interface modules for the assigned theorem: `Sheaf.Paper.FiniteModelConstantScalarExtensionCore` isolates the lifted constant-realization comparison, and `Sheaf.Paper.FiniteModelCoefficientTransport` isolates transport of the canonical derived representative through the coefficient ring equivalence. The assigned module imports these modules and composes their isomorphisms. Its public theorem statement is unchanged.

## Proved and sorry left

The assigned theorem `AlgebraicGeometry.Scheme.finiteModel_derivedScalarComparison` is proved. Two strictly simpler intermediate theorems remain as named `sorry`s: `AlgebraicGeometry.Scheme.finiteModel_constantScalarExtension_core` and `AlgebraicGeometry.Scheme.finiteModel_derivedRepresentative_transport`, with nodes `lem-weil-pbc-finite-model-derived-scalar-comparison-core` and `lem-weil-pbc-finite-model-derived-scalar-comparison-transport`.

## No longer needed

No previously imported proof dependency was removed. The parent proof now uses only the two new interface nodes; the original lower plan declarations are represented by those interfaces and are not imported directly by the assigned module.

## Where the brief, the DAG or earlier work was wrong

The original module had one monolithic upper-level `sorry` despite the DAG proof having two independent interfaces. The proof is decomposed into the constant-realization comparison and the coefficient-transport comparison, each strictly simpler than the target and composed by an explicit Lean isomorphism chain.

## New nodes

`lem-weil-pbc-finite-model-derived-scalar-comparison-core` is carried by `lean/Sheaf/Paper/FiniteModelConstantScalarExtensionCore.lean`.

`lem-weil-pbc-finite-model-derived-scalar-comparison-transport` is carried by `lean/Sheaf/Paper/FiniteModelCoefficientTransport.lean`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteModelCoefficientTransport": "c9bba445aa9cad95744612d291cb50d9bf4182e9", "Sheaf.Paper.FiniteModelConstantScalarExtensionCore": "ddfa6f5d8ea699c21c0829dd9100ab4cf828cddd", "Sheaf.Paper.FiniteModelDerivedScalarComparison": "222cfe6c493a3fbd26fecbade15607f09975ec97"}, "results": {}, "time": "2026-10-28T00:20:56+0800", "transitive": 0, "version": 1}
```

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
