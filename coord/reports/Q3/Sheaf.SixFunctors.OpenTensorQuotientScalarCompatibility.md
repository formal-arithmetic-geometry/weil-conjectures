## What changed

Repaired `WeilConjectures.OpenTensorQuotient.ScalarCompatibility` in
`Sheaf.SixFunctors.OpenTensorQuotientData` by retaining the missing finite generator
normalization as `sections`. It sends each finite extension summand to the identical
summand after scalar restriction. All previous fields and the strict-system evaluation
equation remain. The shared data module was unclaimed on the live server.

Proved `openQuotientScalarUnitEquation` by evaluating a tower map at a level and degree,
using `r.components`, applying open-extension generator extensionality, then composing
`tc.generators`, `sc.sections`, and naturality of extension generators. The proof imports
`OpenScalarTransitionCompatibility` and `OpenFiniteScalarComparison` privately with
`import all` to reuse their already proved private generator helpers. The existing
existential assembly `openQuotientScalarUnitCompatibility` keeps its exact signature.

Updated the definition node, its complete citer audit, and the unit-equation proof plan.
Change record: `coord/changes/Q3-open-scalar-generator-normalization.md`.
No source-library module is edited; the blueprint unit's route is retained.

Validation: the repaired data module compiled in 19.5 s (a set compile also passed
in 40.9 s). The final item compiled without warnings in 17.4 s. All nine direct
importers of the data module passed against the repaired interface: the item,
OpenQuotientScalarComparisonExistence (3.0 s), OpenQuotientScalarCompatibilityData
(2.9 s), OpenTensorQuotientCoefficientComparisons (33.3 s), OpenTensorQuotientGeometry
(17.8 s), OpenTensorQuotientRoosNormalization (20.4 s), OpenFactorQuotientRealization
(22.5 s), OpenTensorQuotientCochains (43.3 s), and OpenTensorQuotientAugmentation
(5.7 s). Each was compiled individually in import order through lcompile.py.
Unchanged verification copies were removed from the sandbox after checking.

## Proved and sorry left

The item starts with one hole, `WeilConjectures.OpenTensorQuotient.openQuotientScalarUnitEquation`
(node `lem-sf-open-quotient-scalar-unit-equation`). Its repaired normalized-interface
statement is proved by the generator calculation. Item holes: 1 before, 0 after.
No holes are added or split off, and no `sorry` is left in either edited module.

The existing dependency holes `openQuotientScalarCompatibilityData`
(`lem-sf-open-quotient-scalar-compatibility-data`) and
`openQuotientScalarComparisonExistence` (`lem-sf-open-quotient-scalar-comparison-existence`)
remain in their existing modules. The former now requires the promised generator
normalization because of the repaired structure; that strengthened obligation is
explicitly retained and is not counted as closed. No new theorem merely relocates
an obligation. The existing data-existence docstring already specifies identity
on extension summands, which is exactly the new field.

## No longer needed

None. No imports, declarations, modules, nodes or unit steps are withdrawn. The two
existing existence lemmas remain necessary for the unchanged existential assembly.
The extra private proof imports supply proved generator extensionality and naturality;
their broader public theorems are not used by this proof.

## Where the brief, the DAG or earlier work was wrong

The previous scalar-data interface did not encode its claimed normalization.
STATEMENT-DISPUTED (previous interface, repaired here): multiplying both `sc.finite`
and `sc.systems` by minus one preserves the old evaluation field. Negating `r.iso`
then preserves its component formula while reversing the unit composite. For the
identity open over a point, residue characteristic 3, and a nonzero degree-zero
module, the scalar unit is not its negative. Thus the old universal assertion
for arbitrary recorded comparison data was false. The finite generator field
restores exactly the comparison intended by Stacks 03DI/03DA/0E8I, without assuming
the desired unit equation. It also covers zero modules, empty and identity opens,
level zero, and negative cochain degrees.

The current queue is a proof item, not a zero-hole repair. The historical global
build-error record names a bad import of `OpenTensorQuotientData`; that dependency
is present and compiled from current source for this packet. No import-collision
rename is needed. The definition repair is reviewed with its downstream users.

## Related modules compiled before delivery

8 related module(s) compiled against this delivery by deliver3.py: 8 OK.

```json
{"capped": false, "direct": 8, "left_out": 0, "own": {"Sheaf.SixFunctors.OpenTensorQuotientData": "80c7d41adbb883589c4635396cec8106cc109c49", "Sheaf.SixFunctors.OpenTensorQuotientScalarCompatibility": "25a6d99b15b1cd8cb6e6e31e30d0a6e5a45106e1"}, "results": {"Sheaf.SixFunctors.OpenFactorQuotientRealization": {"hash": "68a3d8246c930ac0d6d054bf01f6f229d1ecf41e", "status": "OK"}, "Sheaf.SixFunctors.OpenQuotientScalarComparisonExistence": {"hash": "ed678ddd3345cec4e38c0ac85dc8f6d5441c987c", "status": "OK"}, "Sheaf.SixFunctors.OpenQuotientScalarCompatibilityData": {"hash": "a5b8f8c4087f16bdf8077f16e6f26b376d89a253", "status": "OK"}, "Sheaf.SixFunctors.OpenTensorQuotientAugmentation": {"hash": "d904f1c4144df41fb8695b22e9e9ff731efa2b47", "status": "OK"}, "Sheaf.SixFunctors.OpenTensorQuotientCochains": {"hash": "87ce5d0d62cc2097a2fb8d472226a6c55794d836", "status": "OK"}, "Sheaf.SixFunctors.OpenTensorQuotientCoefficientComparisons": {"hash": "4e4d8189f0badec569cc53c51c0ae0018049c11b", "status": "OK"}, "Sheaf.SixFunctors.OpenTensorQuotientGeometry": {"hash": "d54cdc02726063dde89125f9cc7b7c23fe42f86f", "status": "OK"}, "Sheaf.SixFunctors.OpenTensorQuotientRoosNormalization": {"hash": "cf3729f2bee2f45f20c2a4a8d49551a96c094077", "status": "OK"}}, "seconds": 141, "time": "2026-10-28T02:18:58+0800", "transitive": 0, "version": 1}
```

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
