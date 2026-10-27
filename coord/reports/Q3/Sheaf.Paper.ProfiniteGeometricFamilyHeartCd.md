## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.profinite_geometric_family_serreHeart_cohomology_vanishes` in `Sheaf.Paper.ProfiniteGeometricFamilyHeartCd`, preserving its statement and every public import. The proof follows all four planned steps. Private proved helpers restrict constant-model generators and their weak Serre coproduct closure, bound the geometric fibres of affine opens, and compare ordinary derived evaluation at an open with derived sections after actual module pullback. The last comparison uses the exact extension-by-zero adjunction to preserve injectives. The two existing vanishing inputs are imported privately. Updated the item's DAG proof and dependencies to these actual inputs.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.ProEtale.CondensedRing.profinite_geometric_family_serreHeart_cohomology_vanishes` (node `lem-sfb-profinite-geometric-family-heart-cd`). No sorry remains in the delivered module. Added 0 holes, split off 0 statements. All six private helpers are proved. The existing affine and affine-to-global theorems retain their separately owned proof obligations; this delivery proves the item from those declarations as instructed.

## No longer needed

Removed private imports `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact` and `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison`. The former's node `det-prop-sfb-module-pullback-exact-main` is not needed here: exactness is already supplied by proved source-library instances for the actual module pullback. Removed its obsolete tool-use approval from this node. The latter's node `lem-weil-pbc-proetale-ringed-open-comparison` is not used directly here: the open evaluation comparison is proved for the actual internal-module functors using extension along an invertible coefficient map, the abelian localization comparison, and preservation of injectives. It remains a dependency of the existing affine-to-global theorem, so its module is not globally pruned. No other dependency, source-library declaration, or module is withdrawn. The finite-type, open-immersion, geometric-fibre and dimension nodes remain used. The constructibility definition remains a statement dependency, while its restriction argument now uses the existing Zariski-locality theorem.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically usable. Two Lean interfaces require explicit glue: the affine input uses integer homology of unbounded derived sections, while the global input uses natural-number classical derived evaluation; and the ringed-open comparison is stated for sectionwise modules, while this item uses internal module objects. The proved private helpers supply these comparisons without new assumptions or new holes. The inherited source gap for the full norm-topological coefficient theorem remains in the affine input and is not presented as resolved by this assembly. No target, definition, coefficient topology, universe, or public signature changed. The current blueprint refinement proof and unit record were read; this proof keeps the affine-to-global route below that unit.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
