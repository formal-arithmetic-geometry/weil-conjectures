## What changed

Proved `AlgebraicGeometry.ProEtale.properHeartBoundLattice` with its signature and public
imports unchanged. The proof constructs the canonical integral reduction tower, uses
constant-model completeness on the finite-type source, and applies exact forgetting,
weakly-etale restriction and derived sections to its Roos triangle. Each reduction is
identified with the quotient lattice in `properHeartBoundTorsion`. Exactness of the
homology sequence kills the limit in degrees greater than `2d+1`. The negative-dimension
case is proved by showing the source empty.

The proved private helpers implement product preservation, transport of Roos triangles,
constant-model completeness of the lattice extension, and comparison of the two existing
reduction conventions. No public declaration, definition or consumer was changed.
The node's proof, proof dependencies and proof origin now describe this realization.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.ProEtale.properHeartBoundLattice`
(`det-proper-heart-bound-lattice`). Original holes: 1; holes closed: 1; holes added: 0;
holes left in the delivered Lean file: 0. No statements were split off. Existing imported
statements retain their existing proof status.

## No longer needed

The following old direct proof imports are removed. Several still occur transitively;
this report claims removal from this proof's direct dependencies, not global withdrawal.

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
- `Mathlib.CategoryTheory.MorphismProperty.Composition`
- `Mathlib.CategoryTheory.MorphismProperty.Limits`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `Sheaf.CategoryTheory.Sites.RGammaDerivedLimit`
- `Mathlib.Topology.KrullDimension`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `Sheaf.CategoryTheory.KInjectiveComputes`
- `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`
- `WeilConjectures.CategoryTheory.Triangulated.MilnorSequence`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.Paper.IntegralModels`

The old route through `sk-lem-integral-models` / `Sheaf.Paper.IntegralModels` is replaced
by the already proved constant-model constructibility and completeness helpers.
`det-pe-products-derived` / `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived` is replaced
by the generic countable-product existence and properties theorems and repleteness.
`lem-kun-site-rgamma-derived-limit` / `Sheaf.CategoryTheory.Sites.RGammaDerivedLimit` is
replaced by the existing derived constant-sheaf adjunction and the explicit image Roos
triangle. `lem-pc-derived-limit-milnor-sequence` /
`WeilConjectures.CategoryTheory.Triangulated.MilnorSequence` is unnecessary: the
zero-outer-terms case follows directly from the Roos triangle's homology exact sequence.

`lem-weil-proetale-weakly-etale-localization` is also unnecessary as a direct input: the
existing generic `upperStarIsoLocalizationRestriction` supplies the product comparison.

The coefficient-ring comparison detour is unnecessary because the proof forgets the
coefficient action before applying derived sections. Thus it does not use
`lem-pur-site-restriction-module-adjunction-exact`,
`lem-sfb-proetale-object-inverse-image-restriction`,
`prop-pur-kinjective-resolutions-exist`, `lem-sp-grothendieck-enough-injectives`,
`lem-sp-kinjective-computes`, `lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison`,
`lem-weil-pbc-module-sheaves-limits-sectionwise`, or `def-sfb-finite-derived-global-sections`
as direct proof inputs. The relevant exactness and degree-zero comparison are those of
internal module forgetting and Mathlib's exact derived functor API. No module is withdrawn.
The blueprint unit's completeness, torsion and limit argument is retained.

## Where the brief, the DAG or earlier work was wrong

Validation: the complete Lean file compiled with no warnings or errors (37 seconds).

No statement defect was found. The planned proof listed stronger integral-model and
coefficient-ring comparison inputs than needed. The existing finite-model completeness
and torsion theorem's reduction comparison give a shorter realization. Ordinary fibre
dimension is compared with the geometric bound before handling the empty-source case.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
