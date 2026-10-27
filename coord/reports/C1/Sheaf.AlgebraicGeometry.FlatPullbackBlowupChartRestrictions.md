## What changed

Completed `AlgebraicGeometry.Scheme.IdealSheafData.blowup_flat_chart_restrictions` in
`Sheaf.AlgebraicGeometry.FlatPullbackBlowupChartRestrictions`. All public signatures,
definitions, attributes, and public imports are unchanged. The two existing proofs of the
fibre and etale-neighbourhood assertions are unchanged.

Added the proof import
`WeilConjectures.Compactification.StrictTransformChartModel`, which supplies the proved
coefficientwise chart map and its commuting affine chart square. The import-direction
check accepts this import. Six private, fully proved helpers handle flat injectivity,
transport between the equivalent homogeneous chart presentations, the chart square,
preimages of chart opens, images of centre ideals, and ordinary localization of an
equivalence.

The shorter route uses the existing `strictChartMap_surjective` and
`ker_strictChartMap`. Multiplication by the denominator is injective on the chart
subalgebra of its localization. Flatness preserves that injectivity after tensoring;
thus the kernel, which consists of denominator-power torsion, vanishes. The resulting
algebra equivalence has exactly the required fraction formula. The universal property
of blowups identifies the specified global comparison on affine opens. The source's
`isPullback_baseChangeChartι` then supplies its chart square. Standard-open preimages
and injectivity of open embeddings prove the range equality. Ideal-map composition
proves the centre-ideal identity. Localizing the actual equivalence proves the overlap
formula, including its denominator powers.

Updated only the item's DAG node: steps 1--4, their dependency union, proof origin, and
removal of obsolete tool approvals. No other existing module or node is changed.

Validation: remote `lcompile.py` compiled the complete module without warnings in
36.3 seconds, below the 60-second limit. The final delivery runs the required probes.
The argument permits the zero chart ring: nilpotent or zero denominators produce a
zero localization, in which the regular-action argument still applies. No domain,
nonzero-denominator, or residue-field-identification assumption is introduced.

## Proved and sorry left

Closed 1 of the item's 1 starting holes:
`AlgebraicGeometry.Scheme.IdealSheafData.blowup_flat_chart_restrictions`
(node `lem-sfb-flat-pullback-blowup-chart-restrictions`).

Added 0 holes and split off 0 statements. There are 0 remaining `sorry` declarations in
the delivered module and no new modules. This is a proof, not a decomposition.

The previously completed `blowup_flat_fiber_residue` and
`etale_blowup_reduced_point_neighbourhood` remain proved as before.

## No longer needed

No existing Lean imports were removed. The following planned dependencies are removed
from the item's direct `proof_deps` and from its obsolete `tool_uses` approvals:

- `lem-nagata-affine-proj-scalar-extension`
  (`Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension`): the existing chart square
  and the uniqueness of a blowup lift give the global comparison directly.
- `lem-nagata-homogeneous-localization-scalar-extension`
  (`Sheaf.RingTheory.HomogeneousLocalizationScalarExtension`): the existing sigma map
  becomes bijective by its torsion-kernel calculation and flatness.
- `lemma-nagata-extended-ideal-affine-chart`
  (`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`): the required equality
  follows directly from `Ideal.map_map`, algebra compatibility, and the affine comap
  formula. That source module remains needed elsewhere, including by existing imports.
- `lemma-nagata-chart-extended-ideal-principal`
  (`WeilConjectures.Blowup.Affine.Principalization`): no principal-generator calculation
  is needed for the ideal equality. No source declaration or import is withdrawn.
- `lemma-nagata-proj-chart-ring-cocycle`
  (`WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`): the
  requested overlap assertion is the ordinary localization of the actual equivalence.
  That source module still supplies other existing chart constructions.
- `def-nagata-flat-pullback-rees-map` and `lemma-nagata-flat-pullback-rees`: their maps
  are not calculated in this proof. They remain transitive prerequisites of the
  unchanged canonical global comparison, so this does not withdraw their modules.

The two scalar-extension statement modules above are not imported by the new proof.
This is pruning of this item's proof plan; no global loss of reachability is claimed.
The four homogeneous-away/chart identification nodes are retained because the existing
fraction-chart construction uses that equivalence. The unit's statement and route are
unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG's Rees scalar-extension plan was mathematically valid but longer than the
already implemented source API. The strict-chart kernel and surjectivity theorems
provide the shorter route even for zero divisors. All remaining geometric glue is
already proved in the source library.

Some older node attachments lag behind the available source declarations:
`lemma-nagata-strict-chart-map-surjective` points primarily to
`closure_range_awayAlgebraMap_union_range_awayMap`, whereas the exact theorem now used is
`AffineBlowup.strictChartMap_surjective` in
`WeilConjectures.Blowup.Affine.StrictTransformChart`.
`lemma-nagata-strict-chart-map-kernel` is audited closed and its exact existing theorem is
`AffineBlowup.ker_strictChartMap` in the same module. Neither dependency node was edited.
There is no statement dispute or definition repair.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
