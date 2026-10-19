## What changed

Completed `CategoryTheory.site_truncation_isDerivedLimitTriangle` in
`Sheaf.CategoryTheory.SiteTruncationDerivedLimit`, preserving its full signature and all
public imports. The proof constructs the derived product from termwise products of
K-injective resolutions, lifts the compatible truncation maps through the Roos triangle,
and proves the lift invertible on every cohomology sheaf. Uniform stabilization follows
from the existing successive lower-truncation triangle and the given vanishing bound.
Milnor's sequence identifies the eventually stable section-cohomology projections;
exact sheafification and local bijectivity detect the resulting cohomology isomorphisms.
Transport along the lift gives the triangle with exactly the prescribed first arrow.
All implementation helpers are private and proved; their constructions contain no holes.

Added proof imports of `Sheaf.Algebra.Homology.LowerTruncationStepTriangle` and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`. Updated the item's
DAG proof and dependencies to use the already proved lower-truncation-step theorem.
No existing statement, definition, consumer, or public interface changes are included.
The single-file compiler check completed successfully in 12.0 seconds, without warnings.
A source comparison confirmed the theorem signature and all public imports are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.site_truncation_isDerivedLimitTriangle`
(node `lem-kun-site-truncation-derived-limit`). There are zero `sorry`s left in the
item and zero holes added or split off. Every private helper is proved.
The proof uses the existing declared dependencies, as intended by stage 3; it does not
claim to close holes in their transitive dependencies.

## No longer needed

The direct dependency `lem-weil-pbc-complex-ses-triangle`
(`Mathlib.Algebra.Homology.DerivedCategory.ShortExact`) is replaced by the existing
`lem-pc-derived-lower-truncation-step-triangle`
(`Sheaf.Algebra.Homology.LowerTruncationStepTriangle`). The latter supplies precisely
the canonical successive transition, so this module need not repeat the two-term kernel
construction or its short-exact-sequence argument. Removed the former node from the
item's direct proof dependencies and approved tool-use list. Its other users are unaffected.

Removed proof imports:

- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`: retired compatibility module;
  use `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful` directly.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`: already publicly available through
  the existing statement imports and through the forgetful-functor theorem's module.
- `Sheaf.Algebra.Homology.KInjectiveProducts`: empty compatibility module; the termwise
  product theorem is in `Sheaf.Algebra.Homology.KInjectiveProductsTermwise`.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`: its direct SES construction is
  unnecessary with the existing lower-truncation triangle.
- One duplicate `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence` import.

All other planned dependencies remain used. No whole-library module is withdrawn;
public statement imports are preserved. The blueprint unit and chapter route are kept.

## Where the brief, the DAG or earlier work was wrong

The original step 3 repeated an argument already formalized by
`DerivedCategory.exists_lowerTruncationStepTriangle`. Reusing that declaration is a
shorter realization of the same step, without changing the mathematics or unit route.
The existing section functor has the same underlying implementation as forgetting to
abelian sheaves and evaluating; successor maps of `Functor.ofOpSequence` require their
explicit map equation rather than a definitional `change`. The final theorem consistently uses
`siteModuleSections` and its explicit resolution instance, so that the derived section
functor carries exactly the shift structure used by `site_rgamma_derivedLimit`. A local
`backward.isDefEq.respectTransparency false` elaboration option identifies the equivalent
ring-sheaf presentations; no categorical construction or theorem signature is changed.
The first retry of the compiler received no answer from the server; a later retry resumed
normal checking. No launcher script or shared-repository file was changed.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
