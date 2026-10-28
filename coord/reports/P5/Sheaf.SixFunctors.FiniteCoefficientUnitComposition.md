## What changed

Proved `WeilConjectures.finiteCoefficient_unit_composition` with the original
statement and public imports unchanged. Its proof identifies the three normalized
units with exact scalar insertions, proves composition of the ordinary restriction
lax units, and applies `SheafExactDegreeZero.scalarAdjointInsertion_comp`.

Added the fully proved module `Sheaf.SixFunctors.FiniteCoefficientUnitInsertion`,
with public theorem `WeilConjectures.finiteCoefficient_unit_eq_scalarInsertion`.
Its private helpers express the cochain normalization over abstract categories and
keep the representative equation uniform in the complex, avoiding expensive
conversion of concrete monoidal-unit data. Separating this self-contained proved
calculation keeps the individual files within the compile limit after that
conversion improvement. The statement requires neither finite rings nor flat maps.

The new module publicly imports the normalization and exact-insertion definitions,
and uses `import all Sheaf.Paper.ScalarSingleAdjointInsertion` only for its proof's
existing general private adjunction helper. The item imports the new module only
for its proof and also privately imports
`WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf` for the ordinary
restriction-unit calculation. Updated the item's DAG proof to use the new proved
node. No existing module besides the assigned item is changed.

## Proved and sorry left

Closed one existing hole: `WeilConjectures.finiteCoefficient_unit_composition`
(node `lem-sf-finite-coefficient-unit-composition`).
Also proved `WeilConjectures.finiteCoefficient_unit_eq_scalarInsertion`
(node `lem-sf-finite-coefficient-unit-insertion`) and all private helpers.
Added zero holes; zero holes remain in either delivered module. There are no
unproved split-off statements. Both files compiled without diagnostics in import
order: unit insertion in 44.2 seconds and composition in 26.6 seconds.

## No longer needed

None. No original public import, node, module or unit step is pruned. The original
normalization, representative and scalar-single dependencies remain used through
the new proved unit-insertion node; the item uses the exact insertion composition
and the fixed scalar associator directly. The scalar-single proof import resides
in the new module rather than being duplicated in the item.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The existing plan works with `scalarSingleMap_cochain`
and the general adjunction calculation underlying `scalarSingleMap_eq_scalarInsertion`.
The ordinary calculation uses the sheafification-unit extensionality lemma and the
pointwise restriction unit. It covers identity maps, zero rings, arbitrary schemes
and nonflat coefficient maps without extra hypotheses. No target, shared definition
or existing public signature is changed.

## New nodes

`lem-sf-finite-coefficient-unit-insertion` records the fully proved first step of the
item's original argument: the normalized regular-unit hom is the derived adjunction
insertion of the ordinary restriction lax unit. Its source is the regular-unit
quotient compatibility in `lem-coef-integral-finite-extension.proof.md`. The node
has the complete Lean attachment, proof dependencies, source proof and three kinds
of Mathlib search. This is a strictly smaller, proved part of the composition
argument. There are no change records because no other existing module or statement
is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteCoefficientUnitComposition": "5282a5cfabf880a3889c95a0a390f090528af365", "Sheaf.SixFunctors.FiniteCoefficientUnitInsertion": "4897496d21b1d51833c13aaac393e05d44089989"}, "results": {"Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient": {"hash": "185e6c5f41def5451d93ce79e8ead46b994514e8", "status": "OK"}}, "seconds": 43, "time": "2026-10-28T10:51:05+0800", "transitive": 0, "version": 1}
```

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
