## What changed

Filled `coefficient_comm`, `encoding_preservesFlat`, and `pushMap_isIso`; proved the main finite-level projection theorem using existing finite-ring origin, open-extension, and bounded proper projection results. Added private intrinsic-to-etale constructibility bridges. Local irreducibility settings keep the existing tensor and derived operation comparisons from repeatedly unfolding large constructions; their definitions and public interfaces are unchanged. The complete module compiled in 43.5 seconds before removal of profiling/check commands and style-warning cleanup.

## Proved and sorry left

Proved: `coefficient_comm`, `encoding_preservesFlat`, `pushMap_isIso`, `finite_level_projection_factors`. Closed 4 of the original 13 holes; added 0. Remaining 9 holes (all in
`AlgebraicGeometry.ProEtale.FiniteLevelComparison`, node
`lem-sp-finite-level-projection-factors`): `scalarMap_existsUnique`, `encoding_properties`, `monoidal_existsUnique`, `pushMap_existsUnique`, `proper_adjunction_comparison`, `open_adjunction_comparison`, `proper_projection_comparison`, `open_projection_comparison`, `coefficient_models`.

## No longer needed

Removed private proof imports: `Sheaf.Paper.ModuleRingedToposDerivedComparison`,
`Sheaf.Paper.FiniteCoefficientModelComparison`,
`Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian`,
`Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula`,
`Sheaf.SixFunctors.OpenTensorNormalization`,
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`,
`Sheaf.Paper.OpenExtensionConstructibleFiniteTor`,
`Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale`,
`Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`,
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`, and
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.

Removed direct proof dependencies from this node:
`lem-sfb-open-extension-zero-constructible-finite-tor` (the proof uses ordinary finite-ring
open extension instead), `lem-weil-pbc-finite-ring-constructible-derived-origin`
(the exceptional-object comparison supplies the origin),
`det-pe-finite-tor-comparison-noetherian`,
`prop-weil-pbc-inverse-image-modules-exact`, and
`lem-weil-pbc-comparison-direct-image-canonical-mate` (their glue is already assembled by
`ProjectionFormulaBounded`). These are removals from this item's direct proof route;
no claim is made that other consumers no longer need them.

The main proof uses the existing fixed-scalar intrinsic/etale constructibility comparison,
bounded proper projection and ordinary open-extension preservation. It does not use the
internal comparison lemmas in the item to prove the ordinary projection assertion. Those
internal comparison statements and their planned dependencies remain part of the node's
Moreover clause, so they are not withdrawn. Removed imports may remain transitively reachable
from retained public imports or from the source projection theorem. No whole-module pruning
or upstream declaration withdrawal is claimed.

## Where the brief, the DAG or earlier work was wrong

The main target can use the existing ordinary finite-ring proper projection theorem after obtaining an etale origin for the second argument; a new internal adjunction proof is unnecessary for this target.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
