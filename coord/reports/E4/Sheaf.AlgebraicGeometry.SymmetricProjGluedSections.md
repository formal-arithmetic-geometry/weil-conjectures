## What changed

The signature and public import of the assigned theorem are unchanged. Its proof now
constructs the section map by transporting affine linear maps through the twist charts
and extending them from the affine basis. It proves compatibility using the restriction
formula for the symmetric algebra. The exact normalization follows from the normalized
tensor unit.

Two private helpers are fully proved in the item: `affine_linear_maps_glue` extends
compatible affine linear maps, checking linearity on arbitrary opens by sheaf separation;
`twist_chart_read_bijective` proves invertibility of chart reading using the pullback
adjunction unit on the range of an open immersion.

Added proof imports for `SymmetricProjAffineGeneratorLinear`, the source `Modules.PullbackUnit`,
and Mathlib's `SheafCondition.Sites` and `SheafCondition.UniqueGluing`. They supply the affine
formula, open-immersion unit bijectivity, affine-basis extension, and sheaf separation.

The new modules separate object descent, the affine generator calculation, and the
structural coefficient formula. All work is in Sheaf; no source-library declaration,
existing definition, target statement, public import, or consumer is changed.

Validation: `lcompile.py --all` passed all four files in import order. The assigned
module compiled in 13.0 s, affine linearity in 9.9 s, and the structural identity in
54.3 s; object descent reused its earlier successful compile. No compiler warnings remain.

## Proved and sorry left

This delivery is a decomposition. Closed the item's one original hole:
`AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_symmetric_twist_sections`
(`lem-trf-symmetric-proj-glued-sections`). There are zero holes left in the item.

Also fully proved the structural coefficient formula
`AlgebraicGeometry.Scheme.GradedAlgebraData.chart_scalar_value`
(`lem-trf-relative-proj-chart-scalar`) from Mathlib's Proj structure maps and localization
formulas, and the affine generator linear-map construction
`AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_affine_generator_linear`
(`lem-trf-symmetric-proj-affine-generator-linear`) from it.

One hole is added:
`AlgebraicGeometry.Scheme.GradedAlgebraData.exists_twist_chart_descent`
(`lem-trf-relative-proj-twist-chart-descent`): descend the actual affine twists with
compatible transitions. This concerns a general graded algebra and asserts no map from E.
There are no other holes in the four delivered modules. This is one original hole closed
and one strictly smaller object-descent hole added; no net decrease is claimed.

The new obligation does not repeat the assigned theorem. The intervening proof constructs
and glues the actual module morphism. All new definitions have explicit bodies; none
chooses an undetermined object from a mere existence theorem. No private proof has a hole.
Edge cases checked mathematically: empty base or charts, zero ring, E=0, nilpotent
generators, and arbitrary infinitely generated quasi-coherent E. No nonemptiness,
finite-generation, freeness, or invertibility assumption is added.

## No longer needed

No existing module or node is withdrawn, and no original public import is removed.
`lem-weil-pbc-glue-sheaves-of-modules` (`Sheaf.Topology.GlueSheavesOfModules`) and
`lem-sfb-proj-scalar-extension-twist-comparison`
(`Sheaf.AlgebraicGeometry.ProjScalarExtensionTwistComparison`) move from direct proof
dependencies of the item to dependencies of the object-descent statement. They remain
necessary; no transitive pruning is claimed. The original separate pullback
adjunction theorem is used through its existing section-normalized adjunction API.
The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The original plan did not expose a Lean interface for descending twists and reading their
sections coherently. Generic sheaf gluing uses Over sites, while the requested charts
use actual tensor pullbacks. The new object-descent statement records that bridge and
its fraction formula without bundling in the section map. The source's pointwise
unitToTwist formula also needs the structural coefficient formula to establish base
linearity; that ring identity is proved in its own module. No statement is disputed.

The existing creation metadata uses module names rather than node IDs, so
`blueprint_refs.py ancestor` cannot resolve the immediate creation chain. The new nodes
retain the historical blueprint ancestor recorded by the normalized-descent ancestor,
with the intervening nodes listed explicitly. Existing metadata is unchanged.

## New nodes

`lem-trf-relative-proj-twist-chart-descent`, in `RelativeProjTwistChartDescent`, records
object descent and the induced transition maps from Stacks Tag 01NR. Its docstring gives
the comparison maps, affine refinement, cocycle, and tensor-unit identification.

`lem-trf-relative-proj-chart-scalar`, in `RelativeProjChartScalar`, records the structural
coefficient identity of Tags 01ME and 01NQ. Its complete Lean proof uses the defining
D_+(1) structural map, pointwise awayToSection, and preservation of constant fractions
under localization. Local irreducibility attributes prevent unfolding the relative
Proj gluing construction during elaboration and change no shared attribute.

`lem-trf-symmetric-proj-affine-generator-linear`, in `SymmetricProjAffineGeneratorLinear`,
records the affine linear-map construction and its proof from the scalar identity.
No change record is needed because existing shared interfaces are unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.RelativeProjChartScalar": "b5fca515bfb6a8f07c4b3d87939d0f5f5517c8cd", "Sheaf.AlgebraicGeometry.RelativeProjTwistChartDescent": "a8c40b9906b4f2befe885e09401b4099ffd6d70b", "Sheaf.AlgebraicGeometry.SymmetricProjAffineGeneratorLinear": "74780bed89b0aa2341d82f52894ff338fdbb302e", "Sheaf.AlgebraicGeometry.SymmetricProjGluedSections": "27b038f02bff8ac5eef70528b38ab8cf982eeefd"}, "results": {"Sheaf.AlgebraicGeometry.SymmetricProjAffineComparisonExistence": {"hash": "9a2a4852eb33ffbe86fb52289c7593fc2ac8c223", "status": "OK"}}, "seconds": 61, "time": "2026-10-28T00:18:30+0800", "transitive": 0, "version": 1}
```

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
