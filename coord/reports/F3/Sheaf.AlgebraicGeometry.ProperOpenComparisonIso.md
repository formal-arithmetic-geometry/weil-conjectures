## What changed

Proved `AlgebraicGeometry.Etale.isIso_properOpenComparison` with its original signature and
specified `properOpenComparison`. No statement, definition, public import, or consumer changed.
Three proved private helpers establish zero detection on D⁺, derived disjoint-range vanishing,
and invertibility of the specified comparison after restriction to the open.

The argument follows the blueprint's open/outside-open geometric-point cases. The open case
uses the invertible derived adjunction unit and right triangle identity. Outside the open,
the commuting triangle and pullback equation give disjoint ranges; the existing sheaf
vanishing theorem lifts to D⁺ using the exact-functor homology comparisons. The declared
finite-coefficient geometric-fibre theorem then kills the proper pushforward on that point.
The module-valued geometric stalk criterion and `DerivedCategory.Plus.isIso_iff` finish.

Added proof imports `WeilConjectures.SixFunctors.OpenClosed.Complex` and
`WeilConjectures.SixFunctors.OpenClosed.Conservative` for the sheaf unit, disjoint-range
vanishing and stalk/pullback comparison. Kept `Sheaf.AlgebraicGeometry.GeometricFiberFinite`.
Updated the existing node's proof, proof dependencies and origin to this argument, and
removed obsolete tool-use entries. No new nodes and no change records are needed.

Validation: the final module compiled cleanly through `lcompile.py` in 8.9 seconds, with
`autoImplicit = false`, no errors, no warnings and no `sorry` in the delivered source.
The full unit record has no realized statement or proof steps for this node; the blueprint's
proper geometric-fibre and stalk-conservativity route is retained. Checked the empty open,
whole open, empty fibre, arbitrary bounded-below K and the zero coefficient ring: no step
requires a nonempty scheme, nonzero ring, constructibility or finite individual sheaves.

Searches: LeanFinder found Zariski module restriction/pushforward comparisons, not this
étale derived comparison. Loogle confirmed `DerivedCategory.Plus.isIso_iff`. Repository and
Mathlib grep found the existing finite/open comparison proof, exact-functor homology API,
module-valued stalk conservativity and disjoint-range vanishing used here.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_properOpenComparison`
(node `lem-weil-pbc-proper-open-comparison-iso`). Added 0 holes; split off 0 statements.
There are no sorries left in the item's module or added elsewhere by this delivery.
The existing imported `AlgebraicGeometry.Etale.isIso_geometricFiber_finite` remains a stated
proof dependency; it is used as intended by the stage-3 brief, not re-proved here.

## No longer needed

Removed these 14 direct proof imports:

- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.AlgebraicGeometry.OpenImmersionSquare`
- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Mathlib.Algebra.Homology.DerivedCategory.Plus`
- `Sheaf.AlgebraicGeometry.ProperOpenSection`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`

The corresponding declarations that are still used (the derived-category criterion,
exact-functor comparisons, extension-by-zero definitions and stalk criterion) are already
publicly exported by the retained imports. Removing their redundant direct imports does
not claim to remove their modules from the entire target closure.

Removed the following direct DAG proof dependencies:

- `lem-weil-pbc-proper-open-section`
- `def-cbc-open-immersion-square`
- `cor-cbc-derived-extension-zero-base-change`
- `lem-weil-pbc-extension-by-zero-stalks`
- `prop-weil-pbc-geometric-stalks-exact`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-geometric-point-pullback-stalk`

`lem-weil-pbc-proper-open-section` and its module `ProperOpenSection` are unnecessary to
prove invertibility once the specified restriction identification is available. Its geometry
still underlies the definition of `properOpenIdentification`; this delivery does not bypass
that construction. The empty-square route (`OpenImmersionSquare` and
`derivedExtensionZeroBaseChange`) is replaced here by the existing, proved disjoint-range
vanishing theorem. The stalk formula of `FiniteComparison` is replaced by that same vanishing
and pullback/stalk compatibility. Exact pullback and its cohomology comparison let the proof
avoid exact stalk functors, global-sections-to-stalk comparison and the separate constant-ring
`SheafOfModules` inverse-image theorem. `GeometricPointCanonicalGerm` remains a dependency of
`GeometricFiberFinite`, and derived extension-zero base change remains in the comparison
construction; these are not claimed to be globally pruned.

Removed obsolete tool-use approvals for `cor-cbc-derived-extension-zero-base-change`,
`prop-weil-pbc-inverse-image-modules-exact`, `prop-weil-pbc-geometric-stalks-exact`, and
`lem-weil-pbc-geometric-point-pullback-stalk`; retained the existing geometric-fibre approval.
The newly cited unit-isomorphism and disjoint-range vanishing nodes are already Lean-closed
tools, not new obligations or replacements of the unit route.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was required. The old plan over-specified the glue:
the general module-valued stalk criterion already reflects isomorphisms, and exact pullback
allows the outside-open computation before taking cohomology. There is no need to construct
an inverse on underlying abelian sheaves or to use global sections at a geometric point.
The geometric-fibre pushforward needed a local additivity instance, supplied by its existing
bounded-below derived adjunction. The old declaration docstring is preserved as a valid
expanded proof plan; the updated DAG and Lean proof record the shorter implementation.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
