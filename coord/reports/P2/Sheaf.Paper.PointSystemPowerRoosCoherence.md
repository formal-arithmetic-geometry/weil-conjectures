## What changed

The original theorem is assembled from two independent specialization lemmas. Its
strict-to-derived insertion step is proved by localization, using the representative
normalization of the existing `derivedTransport` and the canonical derived compositor.
The two specialization lemmas retain the original insertion and Roos comparison routes.

The original definitions are moved verbatim to `Sheaf.Paper.PointSystemPowerRoosData`
and publicly re-exported by the original module. This makes the specialization modules
importable without a cycle. It changes no signature, construction, universe or target
meaning. No other library module currently imports the assigned module.

Validation: all four modules were accepted by `lcompile.py`. The final assigned
module compiles without warnings in 37.6 seconds. Local irreducibility keeps the
recorded inverse-image and insertion constructions behind their APIs during the
representative rewrites; all profiling options have been removed. A signature
comparison checked all 30 original declarations, and the extracted definition
bodies were checked verbatim against the original module.

## Proved and sorry left

Original hole closed in
`WeilConjectures.PointSystemTransport.PowerRoos.point_system_power_roos_coherence`.
Its proof is a decomposition, not a sorry-free proof of the full mathematical result.
The localization lemma
`WeilConjectures.PointSystemTransport.PowerRoos.derived_transport_coherence_from_strict`
and its private representative lemma `insertion_model` are proved without new holes.

Two holes are added, one per new theorem module:

- `WeilConjectures.PointSystemTransport.PowerRoos.point_power_strict_insertion_specialization`
  (`lem-trf-point-power-strict-insertion-specialization`).
- `WeilConjectures.PointSystemTransport.PowerRoos.point_power_roos_comparison_specialization`
  (`lem-trf-point-power-roos-comparison-specialization`).

The data module and assigned module have zero textual holes. Thus the original
1-hole theorem is reduced to 2 strictly smaller arguments; net textual change is +1
hole. The strict specialization constructs only the original section-normalized
compositors and strict insertion law. The Roos specialization takes those section
laws as hypotheses and constructs the comparison family; it asserts no insertion law.

## No longer needed

Removed the four old proof-only imports from the extracted interface:
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`,
`Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus`,
`Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`, and
`Sheaf.Paper.ExactProductFunctorRoosChainMaps`.
Their mathematical roles remain in the specialization nodes' proof plans; they are
not claimed pruned from the project's mathematics. All original public imports remain
in the data module and are re-exported through the assigned module.

The new statement modules import only the data needed for their statements. The
existing insertion-composition and generic Roos-compositor theorems remain the next
proof dependencies in their DAG plans. No mathematical node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing insertion theorem indexes powers by `r+1`, whereas the assigned interfaces
use recursively defined `pointPower` and independently chosen, uniquely normalized
transports. Their agreement is a real specialization step, recorded in the strict
specialization lemma. The generic Roos theorem gives comparisons for a triple of
functors. The assigned statement needs one family for all powers and the original
right-derived unit. Identifying the triple-wise comparisons with this single normalized
family is recorded in the Roos specialization lemma.

The latest blueprint's Global powers paragraph refers to
`det-thm-tf-uniform-formula-weil`, proof (2), whose composition argument was checked.
Edge checks retain the unit comparisons at m=0 on the Roos side, the first
positive composition at m=1 on the insertion side, and the zero system. There is no
boundedness or constructibility restriction in either specialization.
The prescribed unit route is unchanged. The generic exact-product, inverse-image and
Roos facts used by the new comparison node are tools in the parent's already reviewed
route; their approval can be carried forward by the independent reader.

The existing graph has unrelated cycles and external/missing references below the
coefficient conventions. A traversal checked that no cycle involves any delivered
node and that every direct dependency in this packet exists. These pre-existing
graph issues are not altered by the delivery.

## New nodes

`def-trf-point-power-roos-coherence-data` attaches the unchanged extracted interfaces.

`lem-trf-point-power-strict-insertion-specialization` specializes insertion composition
to the recursive Frobenius powers and the original strict chain transport. It includes
zero-power unit comparisons and the specified finite tensor comparisons, but no derived
insertion law and no Roos comparison.

`lem-trf-point-power-roos-comparison-specialization` constructs one normalized comparison
family for all powers from the site/system/restriction section equations, including its
product, cone and derived compositor equations. Its proof plan compares the generic
triple-wise witnesses by projection, signed-coordinate and unit normalization uniqueness.

`lem-trf-point-power-derived-transport-coherence` records the proved localization step.
It takes the strict chain identity as hypothesis and proves only its derived identity.

Change record: `coord/changes/P2-point-power-roos-data-extraction.md`.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
