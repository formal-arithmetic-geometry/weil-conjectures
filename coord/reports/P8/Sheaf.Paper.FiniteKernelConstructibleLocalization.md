## What changed

Prove `WeilConjectures.finiteKernelConstructibleLocalization` in its existing module,
with its public statement and definitions unchanged. Private helpers normalize the
sheaf kernel adjunction, compare intrinsic and fixed-module derived operations,
transport bounded constructibility and the scalar action, and construct the ordinary
triangle from its actual counit. The supported triangle follows from the ordinary
triangle and the existing abstract recollement theorem. The exact closed counit keeps
its specified termwise formula and signed-shift comparison.

Private comparison definitions use local irreducibility attributes and transparency-respecting
elaboration to avoid unfolding large derived constructions. Profiling output is disabled.

The proof reuses the adopted source library's fixed-coefficient localization and
constructibility results rather than reconstructing those results in intrinsic
coordinates. Update the existing DAG node's proof and dependency list accordingly.

## Proved and sorry left

Closed: `WeilConjectures.finiteKernelConstructibleLocalization` (one original hole).
Added: none. Remaining holes in delivered Lean files: zero. No decomposition.
Validation: the first server compile found four missing local instances in
`kernel_ringed_data`; the pointwise adjunction isomorphisms and the open restriction
additivity are now installed explicitly. Recompile and delivery preflight pending.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift`
- `Sheaf.CategoryTheory.KInjectiveTotalDerivedLinear`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.CategoryTheory.OrdinaryTriangleCounitCone`
- `Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`

The existing ringed open-closed, origin and triangulated-constructibility imports are
retained with `import all` to use their already proved comparison helpers. The two
publicly imported kernel/ambient modules also receive private `import all` access
for their proved comparison helpers. Public imports are retained.

The following planned dependencies are no longer used directly by this node:

- `lem-sf-exact-functor-derived-triangulated`
- `lem-weil-pbc-ring-sheaves-grothendieck`
- `lem-weil-pbc-kinjective-functorial-existence`
- `lem-sp-canonical-right-derived-adjunction-shift`
- `lem-sf-triangulated-right-adjoint`
- `lem-weil-kinjective-total-derived-linear`
- `lem-weil-pbc-complex-ses-triangle`
- `lem-sf-ordinary-triangle-counit-cone`
- `cor-fin-deligne-open-finite-coefficients`
- `prop-weil-pbc-comparison-direct-image`
- `def-weil-proetale-constructible-sheaf`

Remove the obsolete `tool_uses` approvals for the seven dependencies in this list
that previously had them: ring-sheaves Grothendieck, K-injective functorial
existence, canonical right-derived adjunction shift, total-derived linearity,
complex SES triangle, finite-coefficient Deligne open direct image, and comparison
direct image. Retain the approvals of the dependencies still used.

The source library already supplies right-derived functor instances and the fixed-ring
finiteness and localization theorems. Scalar linearity follows by uniqueness of right
adjoints and transport of linear categories. The ordinary triangle follows by completing
the open counit and identifying its cone; the supported triangle then uses abstract
recollement. No source-library declaration or module is removed. Transitive dependencies
of the adopted source results remain needed; this packet claims no wholesale pruning of
those modules.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The planned intrinsic reconstruction is longer than the
route now available through proved fixed-coefficient source results. The ordinary
triangle and its actual adjunction maps are retained before the supported triangle.
The proof treats arbitrary fields and intrinsic bounded constructibility, including the
empty open or closed cases, and introduces no finite-Tor hypothesis.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
