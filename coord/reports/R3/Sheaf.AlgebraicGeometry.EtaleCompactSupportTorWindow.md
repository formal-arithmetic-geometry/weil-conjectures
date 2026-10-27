## What changed

Proved `AlgebraicGeometry.Etale.exists_etaleCompactSupport_torWindow` in
`lean/Sheaf/AlgebraicGeometry/EtaleCompactSupportTorWindow.lean`, retaining its exact
signature. The proof chooses the uniform geometric-fibre bound before all coefficient
and complex choices, extends the model termwise, preserves flatness and constructibility,
proves K-flatness and the original Tor interval, and applies the existing proper finite-Tor
theorem with d=2e. Updated the existing node's proof, proof_deps and proof_origin to this
argument; removed obsolete tool_uses entries without adding or reordering approvals.
The public-import change is recorded in
`coord/changes/EtaleCompactSupportTorWindow-imports.md`.

The proof reuses the source `flat_openImmersionLowerShriek_obj`, the source bounded-flat
K-flat and Tor-amplitude criteria, and the existing stronger local-torsion geometric-fibre
bound. The finite-value/source constructibility comparison and exact-functor homology
isomorphism supply the cohomology assertions. Only the three public imports that support
the theorem's vocabulary remain; new proof imports are private. No definitions or statement
signatures changed, and no adopted-source files changed. There are no current direct Lean
importers of the item; no consumers require adaptation. The DAG parent and unit route are
preserved. The unit record sk-lem-sp-reduction has no individually realized steps to bypass.

Searches: msearch leanfinder for extension by zero preserving flatness and bounded-flat Tor
amplitude returned abstract derived bounds, not this theorem; loogle for finite-limit
preservation and tensorRight found the module flatness criterion; msearch grep found no
combined theorem. Repository rg found the proved source flat-extension lemma and the
existing uniform local-torsion fibre bound, which the proof uses directly.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.exists_etaleCompactSupport_torWindow`
(node `lem-sp-etale-compact-support-tor-window`). No holes remain in the item, no holes were
added elsewhere, and none were split off. This is a proof from existing declarations,
not a decomposition. Dependencies remain as recorded in the updated node.

The single-file remote compilation checks the complete theorem. Its signature was compared
byte-for-byte with the repository version. All Lean lines are at most 100 characters.
The proof includes empty schemes, zero coefficient ring, e=0, a=b, and negative endpoints:
no nonemptiness, nonzero-ring, or positivity of endpoints is introduced. Integer fibre
degrees above 2e are converted to natural degrees only after proving nonnegativity.

## No longer needed

Removed direct imports:

- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`.
- `Sheaf.AlgebraicGeometry.Sites.ProperGeometricFibreTorsionBound`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`.
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `WeilConjectures.ConstructibleSheaf.OpenClosed`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`.

These modules are no longer direct dependencies of this proof; this is not a request to
withdraw them globally. Existing declarations under WeilConjectures are preserved.

Removed proof dependencies:

- `lem-sfb-proper-geometric-fibre-torsion-bound`.
- `lem-weil-pbc-open-immersion-etale`.
- `lem-weil-pbc-etale-site-localization-open`.
- `lem-weil-pbc-etale-inverse-image-restriction`.
- `lem-weil-pbc-ringed-slice-extension-tensor`.
- `prop-weil-pbc-inverse-image-modules-exact`.
- `lem-pc-bounded-above-flat-kflat-site`.
- `def-weil-pbc-direct-image`.

The slice-site localization, inverse-image encodings and ringed-slice tensor bridge are
unneeded because the source flat-extension theorem works directly on ordinary fixed-scalar
etale module sheaves. The ringed-site bounded-above K-flat criterion is unneeded because
the given complex is bounded on both sides and the source generic bounded-flat criterion
uses precisely the statement's categorical K-flat predicate. The old sectionwise-torsion
fibre bound is replaced by its already stated local-torsion sibling. The existing proper
finite-Tor theorem already returns unbounded rightDerivedLowerStar, so no separate
bounded-below/direct-image comparison is required.

Removed obsolete tool_uses entries are exactly those among the removed proof dependencies;
remaining approvals keep their original order. No modules are withdrawn and no DAG nodes
are deleted.

## Where the brief, the DAG or earlier work was wrong

The original Step 1 cited
`exists_proper_geometricFibre_torsion_cohomology_bound`, whose actual Lean hypothesis is
sectionwise torsion, while the item's first conclusion quantifies over all locally torsion
sheaves. Applied that way it would not prove the statement. The existing theorem
`exists_uniform_geometric_fibre_dimension_and_torsion_cohomology_bound` has the needed
local-torsion strength after the proved torsion-characterization equivalence. No theorem
statement was weakened or repaired.

The old Steps 3 and 5 invoked ringed-site SheafOfModules results while the item is stated
using Sheaf (ModuleCat R). Their encoding bridges are unnecessary: the adopted source
already proves flatness preservation and categorical K-flatness in the item's encoding.
The old constructibility step needlessly used coefficient invertibility; open extension
of constructible sheaves needs only the quasi-compact open immersion, automatic here.
The coefficient and characteristic hypotheses are retained and passed to the proper
finite-Tor theorem. Its current signature already uses the unbounded proper direct image.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
