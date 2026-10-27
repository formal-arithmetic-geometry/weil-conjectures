## What changed

Replaced the `sorry` in `scalarUnit_abelianTranspose` with a genuine
extensionality proof. The proof reduces equality of tower morphisms to equality
of their values at each level, pro-etale chart, and section, then invokes the
strictly simpler sectionwise theorem in
`Sheaf.Paper.TowerScalarUnitAbelianTransposeSection`. Added that sectionwise
statement as a split-off node with its source and proof plan. The parent node's
proof and proof dependencies now record this route.

The sandbox compiles both modules with `lcompile.py --all`; the parent theorem
has no remaining `sorry`.

## Proved and sorry left

Proved and closed: `AlgebraicGeometry.ProEtale.SpTowerClasses.scalarUnit_abelianTranspose`
(one of one original holes). Added one strictly simpler hole:
`AlgebraicGeometry.ProEtale.SpTowerClasses.scalarUnit_abelianTranspose_section`
in `TowerScalarUnitAbelianTransposeSection.lean`.

## No longer needed

No public imports were removed because both existing public imports provide
objects used in the target statement. The parent proof no longer directly needs
`lem-sp-tower-integral-class-pullback`; its route is now the sectionwise helper
plus categorical extensionality. No other declared dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan described the section calculation but did not expose
it as a Lean declaration. The target can be assembled from a sectionwise
statement and standard natural-transformation, sheaf, and additive-group
extensionality, so the parent node now records that reduced route. No statement
or definition was changed.

## New nodes

`lem-sp-tower-scalar-unit-abelian-transpose-section` states the equality of the
two abelian-transpose maps on every level, chart, and section. Its source is the
classes proof (2), paragraph (2), in
`sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-classes.proof.md`.
The proof plan uses the ordinary adjunct equations, `CoefficientPullback`
normalization, `IntegralCoefficientPullback.unit_normalization`, and local
surjectivity of the constant integer sheaf; it is strictly below the parent
morphism equality and is left for a follow-up worker.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.TowerScalarUnitAbelianTranspose": "2cace1a9943c2a8d7d5dacdab95b22b9d4fe431b", "Sheaf.Paper.TowerScalarUnitAbelianTransposeSection": "82a603754a3bcc347119cf161c0f252c314f0a5c"}, "results": {}, "time": "2026-10-28T03:38:14+0800", "transitive": 0, "version": 1}
```

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
