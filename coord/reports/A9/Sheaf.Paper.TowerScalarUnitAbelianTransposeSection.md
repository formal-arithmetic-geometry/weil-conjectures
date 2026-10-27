## What changed

Proved `scalarUnit_abelianTranspose_section` by reducing arbitrary coefficient maps to the
canonical maps whose ordinary adjuncts are `scalarGenerator`, using injectivity of the
ordinary hom-equivalences. Added the normalized section calculation as a named split-off
statement in `TowerScalarUnitAbelianTransposeSectionNormalized.lean`.

## Proved and sorry left

The original theorem `scalarUnit_abelianTranspose_section` is reduced to the normalized
subtheorem. The new theorem `scalarUnit_abelianTranspose_section_normalized` remains a
single named `sorry`; it is the strictly simpler normalized ordinary coefficient-unit
calculation described in its docstring. The definition `canonicalScalarUnit` has no `sorry`.

## No longer needed

None. Both original proof imports remain needed, and the normalized module uses both.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan omitted the canonical-normalization reduction as a separate
Lean statement. No mathematical statement was changed.

## New nodes

`lem-sp-tower-scalar-unit-abelian-transpose-section-normalized` records the normalized
subcase and its proof plan.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.TowerScalarUnitAbelianTransposeSection": "973b7c9010a47802cb77c43492cbc0e357eadd01", "Sheaf.Paper.TowerScalarUnitAbelianTransposeSectionNormalized": "3a0fd0aa79c85f3538036f332c6136c51e3a19ba"}, "results": {}, "time": "2026-10-28T06:28:10+0800", "transitive": 0, "version": 1}
```

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
