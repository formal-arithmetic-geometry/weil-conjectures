## What changed

Proved `WeilConjectures.finiteCoefficient_derivedHom_ctf_etale` with its signature unchanged.
The general case reuses the adopted source implementations
`Etale.boundedConstructible_derivedHom` and `Etale.torAmplitudeIn_derivedHom`.
Their finite affine-cover/Verdier-biduality argument follows the unit route. The sharper case
uses `IsSitePerfect.isDualizable` and `torAmplitudeIn_derivedHom_of_isDualizable_aux`.
Two proved private helpers convert bounded constructibility and establish the coefficient
ring's invertible exponent. Their proofs follow the existing private helpers in
`Sheaf.Paper.WeilVerdierPreservationStrata`; no source-library file changes.
A local instance priority aligns the Ring projection for the lifted coefficient CommRing.

Pruned proof imports and redundant public imports, and updated the node's proof route.
The public declaration and all definitions it uses are unchanged. See
`coord/changes/B8-etale-hom-proof-import-pruning.md` for the export change and consumers.

## Proved and sorry left

Closed one hole: `WeilConjectures.finiteCoefficient_derivedHom_ctf_etale`
(node `thm-sf-hom-ctf`). Added zero holes; zero remain in the item. Both private helpers
`WeilConjectures.boundedConstructible_iff` and
`WeilConjectures.coefficient_invertibleExponent` are proved.
This is a proof from existing declarations, not a decomposition. Existing dependencies
are retained with their own proof status; no claim is made that the targets are now closed.

Validation: the first candidate compiled in 29.2 seconds; style warnings were corrected.
The final module and all three unchanged direct consumers compiled successfully with
lcompile.py --all. Their temporary copies were removed after byte-for-byte comparison
with the shared source; only the item module is delivered. The final compile had no
warnings in the item.
The delivery tool performs the final axiom and preflight checks.

## No longer needed

Removed import lines:

- `public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
- `public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `public import Mathlib.AlgebraicGeometry.Sites.Etale`
- `public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`
- `public import WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `public import Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses`
- `public import WeilConjectures.SixFunctors.Etale.Derived.Hom`
- `import Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `import Mathlib.AlgebraicGeometry.Noetherian`
- `import Sheaf.Paper.SiteRestrictionExact`
- `import Mathlib.Algebra.Category.Grp.Abelian`
- `import Mathlib.Algebra.Category.Grp.FilteredColimits`
- `import Mathlib.CategoryTheory.Abelian.ShortExact`
- `import Mathlib.CategoryTheory.Sites.Abelian`
- `import Mathlib.CategoryTheory.Sites.LeftExact`
- `import Mathlib.CategoryTheory.Sites.Over`
- `import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous`
- `import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `import Sheaf.CategoryTheory.RingedToposKFlatPullback`
- `import Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `import Sheaf.Paper.FiniteCoefficientFlatModel`
- `import Sheaf.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFlat`
- `import Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleQcqsAffineLocal`
- `import Sheaf.Paper.FiniteConstructibleHom`
- `import Sheaf.AlgebraicGeometry.OpenImmersionHigherDirectImages`
- `import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `import WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `import WeilConjectures.Algebra.Homology.HomComplex`
- `import Mathlib.Algebra.Homology.HomologySequence`
- `import Sheaf.Algebra.Homology.KFlat`
- `import Sheaf.Paper.EtaleSitePerfectConstructibleHom`
- `import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `import Sheaf.Algebra.Homology.SitePerfectTorWindow`
- `import Sheaf.AlgebraicGeometry.EtaleSheafZeroOnCover`
- `import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact`
- `import Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The following planned dependencies are unnecessary for this module's new proof; their
handwritten ringed-site comparisons and local model arguments are replaced by the proved
adopted source implementations:

- `def-pc-kflat-complex`
- `def-pur-derived-internal-hom`
- `def-pur-hom-complex`
- `def-weil-finite-type-morphism`
- `lem-sf-ext-sheaf-constructible`
- `lem-sf-flat-model`
- `lem-sf-sheaf-zero-on-open-cover`
- `lem-sf-site-perfect-tor-window`
- `lem-weil-pbc-complex-ses-homology-long-exact`
- `lem-weil-pbc-constructible-qcqs-affine-local`
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-weil-pbc-site-restriction-exact`
- `lem-weil-pbc-slice-restriction-flat`
- `lem-weil-pbc-supplied-ringed-topos-kflat-pullback`

Also removed obsolete tool approvals for `lem-weil-pbc-qc-open-immersion-finite-type`
and `thm-constructible-serre`, which supported an abandoned Cech direct-image gluing argument.
The retained geometric dependencies describe the affine reduction inside the reused source
proof. The project module `Sheaf.Paper.FiniteConstructibleHom` is no longer imported here;
the adopted source declaration implements its separated-etale conclusion instead.
No declarations or modules are withdrawn, including any adopted source declarations.
These are dependencies pruned from this item's proof, not assertions that every listed
module is globally unreachable; the ledger determines global pruning.

## Where the brief, the DAG or earlier work was wrong

The old plan reconstructed already-proved source results and its old Lean docstring retained
a Cech/direct-image constructibility argument after the DAG had already switched to affine
locality. The current blueprint explicitly identifies site-perfectness with dualizability;
the proved source bridge supplies precisely the stronger interval without new model lemmas.
The finite-ring constructibility comparison and Tor-predicate equivalence remove the
apparent interface mismatch. Empty X, zero inputs, a=b, c=d and m=0 are covered by the source
proofs and the explicit endpoint inequality. No statement or definition was weakened.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
