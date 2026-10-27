## What changed

Proved `tower_chernReduction_pullback` from invertibility of the canonical
reduction mate, preserving its signature. The new
`Sheaf.Paper.TowerReductionMateInvertible` constructs that mate explicitly
from the localized forgetful square and the two reduction adjunctions.
Its invertibility is the delivery's only postponed statement.

The integer endpoint is proved in the item using the ordinary generator
normalization and the canonical single-complex comparisons. The root endpoint
is proved in `Sheaf.Paper.TowerKummerPullbackTranspose`, using exact-functor
transport of the positive short-exact boundary, naturality under `d.kummer`,
and shift addition. Its private categorical calculations follow the proved
calculations in `NormalizedScalarBoundaryNaturality`, adapted to the actual
Kummer short complex; they use Mathlib `mapShiftedHom_singleδ` and
`ShortComplex.ShortExact.singleTriangle.map`.

The normalization APIs extract the source and target equations before specializing
large coefficient constructions. `Sheaf.Paper.TowerKummerComplex` constructs the
actual Kummer complex, proves its recorded exactness and names its positive boundary
with the literal full-units and roots endpoints. The proved root-normalization
equation shares this construction. A named predicate shares the target-normalization
data, and private typed boundaries fix their literal endpoints. Generic theorems expand normalization
and boundary naturality for complexes constructed from generic endpoints before
specializing the large tower constructions. The private `arrow_normalized_square`
calculation combines boundary arrows and their naturality; typed private root
transposes avoid repeatedly checking the Chern projections. Explicit comparison
lemmas preserve the composition groupings of `derivedUnit`, `derivedRoot`,
`integerDerivedPull` and `unitsDerivedPull`. These local APIs avoid changes to
shared definitions, instances, public imports or consumers.

The combining argument uses injectivity of the adjunction hom equivalence.
It never asserts faithfulness of derived forgetting or evaluation. Proof-only
imports expose the new APIs; redundant direct imports of Mathlib boundary and
source-library exact-functor APIs are unnecessary because the original public
data import already exposes them.

Validation: all eight delivery modules compiled cleanly through `lcompile.py --all`;
the slowest took 32 seconds, below the unchanged 60-second limit. No profiler,
tracing or modified heartbeat options remain. The item signature and original
docstring match the source verbatim; node attachments and dependency unions were
checked against the delivered files.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.SpTowerClasses.tower_chernReduction_pullback`
(node `lem-sp-tower-chern-reduction-pullback`). The item has zero holes left.

Also proved, with zero holes:

- `AlgebraicGeometry.ProEtale.SpTowerClasses.chern_integral_source_normalization`;
- `AlgebraicGeometry.ProEtale.SpTowerClasses.chern_integral_target_normalization`;
- `AlgebraicGeometry.ProEtale.SpTowerClasses.chern_target_normalization`;
- `AlgebraicGeometry.ProEtale.SpTowerClasses.kummer_pullback_transpose`;
- `AlgebraicGeometry.ProEtale.SpTowerClasses.Kummer.shortComplex_exact`;
- `AlgebraicGeometry.ProEtale.SpTowerClasses.chern_root_normalization_equation`.

Added one hole:
`AlgebraicGeometry.ProEtale.SpTowerClasses.tower_reductionMate_isIso`
(node `lem-sp-tower-reduction-mate-invertible`). This is a decomposition,
not a net proof: one hole closed, one added. The new statement is solely
invertibility of an explicitly constructed mate. It has no Chern normalization
hypotheses and concludes neither endpoint equation. The combining proof and
the proved helpers establish those equations.

## No longer needed

No original import was removed and no module is withdrawn. Torsion-action
uniqueness, geometric inverse image and algebra-diagram extension coherence
move under the new mate-invertibility node; they remain needed there.
The exact-functor boundary leaf moves under the proved Kummer-transpose node.
No global pruning is claimed. The source and target normalization definitions
remain used through the new proved APIs.

## Where the brief, the DAG or earlier work was wrong

The algebra-diagram comparison is stated in diagram-site coordinates and does
not directly apply to the recorded reduction and forgetful data. The new mate
node isolates its geometric transport and identification with the canonical
mate. The original endpoint steps are now Lean proofs, including the signed
Kummer boundary and its degree-two shift comparison.

The unit record assigns no realized nodes in these positions. The route through
integral quotient reduction and the Kummer boundary is preserved. Identity
inverse image gives the mate of an isomorphism of reduction right adjoints;
empty schemes give zero categories. No nonemptiness, flatness of f or unramified
E assumption is used. The new mate is constructed before its invertibility is
asserted, and no arbitrary object is chosen from an unproved existence theorem.

## New nodes

`lem-sp-tower-reduction-mate-invertible`, in
`Sheaf.Paper.TowerReductionMateInvertible`, postpones original geometric proof
steps 1--2. Its proof in words specifies sequence-site transport, tensor
comparison, universal-counit transport and identification with the explicit mate.

`lem-sp-tower-chern-integral-normalizations`, in
`Sheaf.Paper.TowerChernIntegralNormalizations`, is the proved source-normalization
projection at abstract coefficient diagrams.

`lem-sp-tower-chern-target-normalization-data`, in
`Sheaf.Paper.TowerChernTargetNormalizationData`, is the proved positive-target
projection at abstract coefficient diagrams.

`lem-sp-tower-chern-target-normalization`, in
`Sheaf.Paper.TowerChernTargetNormalization`, proves its concrete specialization.

`lem-sp-tower-kummer-pullback-transpose`, in
`Sheaf.Paper.TowerKummerPullbackTranspose`, proves the root transpose square from
the two target normalizations and the actual Kummer-sequence morphism.

`lem-sp-tower-kummer-short-complex`, in `Sheaf.Paper.TowerKummerComplex`, constructs
the actual complex and its positive boundary, and proves its recorded short
exactness.

`lem-sp-tower-chern-root-normalization-equation`, in
`Sheaf.Paper.TowerChernRootNormalizationEquation`, unfolds target normalization
into the equation for its adjunction transpose and signed shifted boundary.

The six proved auxiliary nodes add zero holes. No existing module interface
changes, forced adaptations or change records are required.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
