## What changed

Replaced the assigned hole by a reduction to stage representation for the existing general spectral-limit
class-lifting theorem to explicitly constructed punctured compact-open neighborhoods.
`PuncturedNeighborhoodInverseLimit` now imports the existing
`PuncturedNeighborhoodSpectralSystem` and reuses its index, directedness, spectral stages
and maps, compatible-tuple limit and initial topology through the ambient-open interface. `OpenSystemRestrictionPresentation` constructs
actual inverse images, unit-preserving composition isomorphisms, transition f-maps and
constant coefficients, and proves their sectionwise compatibility laws.

`OpenSystemColimitCohomologyComparison` constructs the constant-colimit isomorphism and
states its cohomology transport equation. `PuncturedNeighborhoodLegOpenSubspaceComparison`
states the open-subspace cohomology isomorphism and its factorization of the specified
cocone leg. Both are genuine smaller comparison steps. The isomorphism is specified by
its canonical forward map, so no arbitrary data is chosen from an unproved existence.
`CanonicalCohomologyPullbackNormalization` proves the canonical family's IsPullback
property directly from Classical.choose_spec of its defining existence theorem.
`PuncturedNeighborhoodSpectralClassStageLift` states stage representation for the explicit
restriction system; the application of the existing spectral-limit theorem remains open.

No existing signature, definition or public import changed. The inverse-image composition
and constant-colimit isomorphisms are irreducible to bound elaboration.

## Proved and sorry left

Closed the one original textual hole:
`TopCat.puncturedNeighborhood_cohomology_class_lift`, node
`lem-weil-pbc-punctured-neighborhood-cohomology-class-lift`.

Added three holes:
`TopCat.OpenSystem.coefficientColimit_cohomology_comparison`, node
`lem-weil-pbc-open-system-colimit-cohomology-comparison`; and
`TopCat.puncturedNeighborhoodLeg_openSubspace_comparison`, node
`lem-weil-pbc-punctured-leg-open-subspace-comparison`.
The first only transports a coefficient map through a constant-colimit isomorphism;
the second only localizes cohomology to one open and identifies its canonical map.
Neither comparison asserts existence of a lifted class, spectrality or a spectral limit.
The third is `TopCat.punctured_spectral_class_stage_lift`, node
`lem-weil-pbc-punctured-spectral-class-stage-lift`. It is stage representation for the
explicit coefficient colimit before either cohomology or cocone-map comparison. Its
statement has no ambient object-cohomology class or specified cocone leg; these are
combined by the complete item proof. This is a decomposition: one hole closed, three
added, not a net proof gain.

All other new declarations are proved. In particular
`TopCat.objectCohomologyPullback_normalized` is proved. No sorry occurs in any definition,
private lemma or partial proof. Explicit constructions and uniquely determined
universal-property isomorphisms supply all data.

## No longer needed

The now-unused direct proof import `CanonicalCohomologyPullbackNormalization` was removed
from the item; it remains used by stage representation. No original public import,
module, declaration or global mathematical ingredient was
withdrawn. The original localization and composite-pullback dependencies now occur only
in the smaller localization step. The spectral directed-limit ingredient is used through the existing
spectral-system module; inverse-image and colimit ingredients occur in the coefficient setup.

During construction unused imports of `SpectralLimitCohomologyMap` and
`Mathlib.CategoryTheory.Adjunction.Additive` were removed from the restriction-presentation
module. The cohomology-map import is explicit in its actual users. An unsubmitted generic
`OpenSubspaceCohomologyComparison` was replaced by the concrete punctured-neighborhood
localization lemma, avoiding repeated expensive inclusion conversions.

Repair of the return at d311479effe: removed the duplicate
`TopCat.puncturedNeighborhoodIndex` declaration, without renaming it. The new geometry
module publicly imports `PuncturedNeighborhoodSpectralSystem`, where the index already
exists. Its corresponding geometry theorems are reused rather than proved twice.
Direct imports of `WeilConjectures.Topology.SpectralGeneralizations` and
`Sheaf.Topology.SpectralDirectedLimit` and the redundant direct Mathlib spectral imports
were removed. The generalizations-intersection node is no longer a direct dependency
of our adapter; the existing spectral-system proof supplies the needed geometry.

## Where the brief, the DAG or earlier work was wrong

The returned packet duplicated the existing index because it did not reuse the current
spectral-system module. This repair removes that declaration, imports the existing one,
and updates the geometry node and its Lean attachment accordingly. Comparison with the
current shared source confirmed that this module is available and introduces no import cycle.

The plan is mathematically sound, but object-localization AddEquiv identifies a slice
site and supplies no naturality square with the normalized topological pullback used
by the general spectral-limit theorem. The remaining localization comparison states the
needed exact map equation. The coefficient-map transport proof was reduced to adjunction
cancellation and ordinary functoriality, but concrete kernel conversions exceeded the
fixed time limit, so this step remains separately stated.

The newest unit blueprint in literature/blueprint/latest was read. Its route stays.
Edge cases checked: empty space, Z empty or all of T, empty punctured stages, q=0 and
zero coefficients. The index contains the whole-space neighborhood; no point or subspace
is assumed nonempty. The localization isomorphism's canonical forward map determines it.

Searches: LeanFinder found condensed locally constant diagram results, not this
cohomological specialization. LeanSearch found scheme restriction comparisons and inverse
image adjunctions. Loogle found colimit uniqueness equations. Grep found the proved
spectral generalizations and punctured-dimension constructions and object-localization
AddEquiv, but no normalized open-subspace comparison square.

## New nodes

`lem-weil-pbc-punctured-neighborhood-inverse-limit` records the proved geometric data.

`lem-weil-pbc-open-system-restriction-presentation` records the proved coefficient
construction and its compatibility laws.

`lem-weil-pbc-open-system-colimit-cohomology-comparison` records the constructed colimit
isomorphism and the remaining coefficient-map transport step.

`lem-weil-pbc-canonical-topological-pullback-normalization` records the proved normalization
property of the canonical cohomology family.

`lem-weil-pbc-punctured-leg-open-subspace-comparison` records the remaining localization
isomorphism and factorization of the specified canonical leg.

Change record: `coord/changes/J8-punctured-neighborhood-restriction-presentation.md`.

`lem-weil-pbc-punctured-spectral-class-stage-lift` records stage representation before
comparison to ambient object cohomology and the specified cocone leg. It is the third
remaining step, reduced to the existing general spectral-limit theorem and the proved
geometric and coefficient data.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
