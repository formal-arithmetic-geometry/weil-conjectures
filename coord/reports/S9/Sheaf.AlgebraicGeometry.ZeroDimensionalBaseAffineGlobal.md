## What changed

Proved `AlgebraicGeometry.proEtale_cohomology_vanishes_of_affine_of_zeroDimensional_base`
in `lean/Sheaf/AlgebraicGeometry/ZeroDimensionalBaseAffineGlobal.lean` with its public
signature unchanged. Added proved private helpers for total-space dimension,
module/abelian derived evaluation, exactness on an arbitrary open basis, and the Zariski dimension
bound. Updated the theorem docstring and its existing DAG node to describe this proof.
No other Lean module, public declaration signature, or definition was changed.

Repair of the return at `3948694bf`: removed the duplicate scheme-specific private
`AlgebraicGeometry.exact_of_affine_sections`. Its replacement,
`AlgebraicGeometry.exact_of_basis_sections`, is genuinely more general: it accepts
any topological space and any basis of its opens, with explicit space, topology,
basis and basis-proof binders. The comparison proof specializes it to the affine
basis. The existing `AlgebraicGeometry.Scheme.exact_of_affine_sections` in
`Sheaf.AlgebraicGeometry.Sites.AffineToGlobalTorsionCohomologicalDimension` is private
and cannot be imported as an API. No existing library declaration was modified.
The generalized criterion needs neither a scheme nor affine opens, and also covers
empty spaces (where the local-surjectivity condition has no points to check).

The proof uses the existing source-library field-extension dimension theorem and
spectral-sequence rectangle bound. It checks a pushed-forward injective resolution
on affine opens directly. For module coefficients it transports to `ULiftHom` of the
pro-etale site before applying the existing arbitrary-ring injective-module acyclicity
and derived-evaluation theorems. The spectral-space cohomology theorem is applied to
`ULift X`, preserving the original coefficient universe.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.proEtale_cohomology_vanishes_of_affine_of_zeroDimensional_base`
(node `lem-sfb-zero-dimensional-base-affine-global`).

Added 0 holes; split off 0 statements. There are 0 `sorry` tokens in the delivered Lean
module. All private helpers are proved. The existing dependency
`TopCat.Sheaf.subsingleton_H'_top_of_spectralSpace_of_dimension_le`
(node `lem-sfb-spectral-space-cohomology-dimension`) remains an imported stated input;
this delivery does not claim to prove it.

Validation: the module is compiled with the project-server `lcompile.py`; delivery
runs its independent consumer, node, axiom and preflight checks. The original and final
public theorem signatures were also compared byte-for-byte, and all Lean lines are at
most 100 characters.

## No longer needed

Removed these 17 original direct proof imports:

- `Mathlib.AlgebraicGeometry.Properties`
- `Mathlib.Topology.Spectral.Basic`
- `Mathlib.AlgebraicGeometry.Fiber`
- `Sheaf.AlgebraicGeometry.DimensionExtension`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `Sheaf.CategoryTheory.Sites.ModuleDerivedEvaluationSlice`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites`
- `WeilConjectures.CategoryTheory.SiteMorphismComposition`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf`
- `Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`
- `Mathlib.CategoryTheory.Sites.Sheafification`
- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`

Removed these original proof dependencies (and their obsolete top-level tool approvals)
from the item node:

- `lem-kun-dimension-extension`
- `lem-pur-ringed-site-grothendieck-abelian`
- `lem-pe-ringed-site-derived-evaluation-slice`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-weil-pbc-proetale-ringed-open-comparison`
- `def-weil-pbc-site-comparison-morphism`
- `lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites`
- `lem-weil-pbc-site-morphism-composition`
- `lem-weil-pbc-site-pullback-abelian-exact`
- `lem-weil-pbc-site-higher-direct-image-sheafified-presheaf`
- `lem-weil-pbc-cohomology-over-object-localization`
- `thm-sp-grothendieck`
- `def-weil-pbc-sites-and-cohomology`

`DimensionExtension` is replaced by its already proved source-library field-extension
input; no dense-open dimension result is needed. The module and slice comparisons
are replaced by direct comparison at each object. The abstract site-morphism
composition and pullback statements are replaced by continuous functors, exact
filtered Kan extension, and Mathlib sheafification. Direct exactness on the affine
basis replaces the higher-direct-image sheafification and localization statements.
The source-library spectral-sequence bound replaces the project Cartan–Eilenberg
spectral-sequence presentation. Enough injectives for sectionwise modules is transported
from internal modules, so the separate localized-generator theorem is unnecessary.
Site-covering conventions are not used by the proof.

These are removals from this proof, not assertions that the modules are globally
unreachable. Existing public imports are retained. In particular the ringed-open
comparison remains a statement dependency and a public import for the existing
interpretation and interface, although its theorem is no longer used in this proof.
The returned packet's duplicate `AlgebraicGeometry.exact_of_affine_sections` is
removed in favor of the general basis criterion; it was never landed and has no
external consumers. No module is withdrawn and the compactification-coherence unit
route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned module-derived-evaluation slice theorem has a single site/coefficient
universe, whereas this item has pro-etale homs in universe `u` and coefficient groups
in universe `u+1`. Applying it directly would not typecheck. Transporting the topology,
ring and modules to `ULiftHom` supplies an equivalent small site with matching
universes; its forgetful sections agree with the original sections. Similarly the
spectral-space theorem has equal space/coefficient universes, handled by the
homeomorphism `ULift X ≃ₜ X`. No mathematical statement needed repair.

The DAG's proposed sheafification calculation and project spectral-sequence
presentation were longer than necessary given the existing proved source-library API.
The source argument checking exactness on affine opens in
`Sheaf.AlgebraicGeometry.Sites.AffineToGlobalTorsionCohomologicalDimension` applies
without its main theorem's Noetherian or torsion assumptions. The returned packet
restated its private affine-basis exactness theorem verbatim. The repair removes
that duplicate and proves the general topological-basis criterion instead, then
specializes the basis parameter. This is a real generalization of the statement,
not a renaming or an alteration of implicit binders.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
