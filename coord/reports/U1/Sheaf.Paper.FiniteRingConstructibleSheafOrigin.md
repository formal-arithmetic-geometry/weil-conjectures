## What changed

Proved `AlgebraicGeometry.Scheme.finiteRing_constructibleSheaf_origin` without changing
its signature or any existing definition. Reused the existing fixed-module constructible-origin
result instead of repeating its stratified descent argument. Constructed restriction to the
canonical constant scalars, proved it is an equivalence, proved compatibility with canonical
module pullback, and proved equivalence of the two constructibility predicates. The final
subcategory equivalence uses the existing fully faithful comparison pullback. Its additive
comparison is the inverse encoding counit; sectionwise linearity proves the exact scalar formula.

New modules:

- `Sheaf.Paper.ProEtaleConstantModuleEncoding`: explicit restriction functor and proved equivalence.
- `Sheaf.Paper.ProEtaleConstantModulePullbackEncoding`: proved canonical pullback compatibility,
  via the sectionwise direct-image identity and uniqueness of left adjoints.
- `Sheaf.Paper.ProEtaleConstantModuleConstructibility`: proved local constancy, stalk finiteness,
  and global stratified constructibility compatibility. Its private constant-model comparison
  is constructed using module sheafification; it does not choose arbitrary data from existence.

The existing module's four public imports are unchanged. New dependencies are proof imports.
Updated its docstring and DAG proof to the actual shorter route. No statement/definition repair,
change record, withdrawal, consumer adaptation, or forced adaptation is required. The unit's own
statement and realized steps stay unchanged.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.finiteRing_constructibleSheaf_origin`.
Added 0 holes; split off 0 unproved statements. No `sorry` remains in any delivered module.

Also proved the new public theorems:

- `AlgebraicGeometry.Scheme.proEtaleModuleRestriction_isEquivalence`.
- `AlgebraicGeometry.Scheme.proEtaleModuleRestriction_pullback`.
- `AlgebraicGeometry.Scheme.proEtaleModuleRestriction_constructible_iff`.

This is a proof from existing declared dependencies, including the fixed-module descent theorem
and the finite-level clause of `proEtale_profinite_coefficient_inverse_image`; it does not claim
that all imported obligations elsewhere in the library are already closed.

Validation: all four modules compiled together with `lcompile.py --all` in import order.
The construction allows the zero ring. Empty covers and empty strata require no nonzero
constant models. A zero-stratum fixed partition forces the scheme empty; the proof replaces it
with a one-stratum identity partition and uses the empty covering to obtain finite local models.
No arbitrary immersion with full image is asserted to be an isomorphism. Scalar compatibility
is the actual module-linear map law, with the specified sheafification-unit scalar action.

## No longer needed

Removed these direct proof imports from the assigned module:

- `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum`.
- `Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.
- `Mathlib.CategoryTheory.Abelian.RightDerived`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `Mathlib.AlgebraicGeometry.Morphisms.Integral`.
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequence`.
- `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.

The following original direct proof dependencies are not needed by this module's shorter proof:

- `lem-weil-pbc-finite-locally-constant-module-values`.
- `lem-weil-pbc-comparison-pullback`.
- `lem-sf-proetale-locally-constant-origin`.
- `def-weil-pbc-site-comparison-morphism`.
- `lem-weil-proetale-weakly-etale-localization`.
- `lem-cbc-proetale-stalk-conservative`.
- `lem-sf-derived-ses-triangle`.
- `lem-sf-exact-functor-derived-triangulated`.
- `thm-weil-pbc-site-comparison`.
- `def-weil-triangulated-category`.
- `lem-sf-triangle-morphism-iso`.
- `lem-sf-derived-homology-long-exact`.
- `lem-sf-derived-concentrated-single`.
- `lem-sf-constructible-partition-local-closed-stratum`.
- `lem-weil-pbc-immersion-base-change-lft`.
- `def-weil-constructible-subset`.
- `def-weil-closed-immersion`.
- `lem-sf-proetale-open-closed-sequence`.
- `lem-cbc-proetale-extension-zero-comparison`.
- `lem-weil-pbc-closed-immersion-integral-separated-uc`.
- `lem-weil-pbc-affine-morphism-permanence`.
- `prop-weil-pbc-comparison-direct-image`.
- `lem-weil-pbc-left-exact-injective-resolution-degree-zero`.
- `lem-weil-pbc-ring-sheaves-grothendieck`.
- `lem-sp-grothendieck-enough-injectives`.
- `def-weil-pbc-proetale-modules`.

The old derived-extension and open/closed descent plan is replaced by the existing fixed-module
constructible-origin theorem plus the explicitly proved coefficient identifications. Some old
nodes remain needed transitively inside that source theorem or elsewhere in the target closure;
this report claims removal of this item's direct dependencies, not global unreachability.

Withdrawn obsolete top-level `tool_uses` approvals (in the old order):

- `lem-weil-pbc-finite-locally-constant-module-values`.
- `lem-sf-proetale-locally-constant-origin`.
- `lem-weil-proetale-weakly-etale-localization`.
- `lem-cbc-proetale-stalk-conservative`.
- `lem-sf-derived-ses-triangle`.
- `lem-sf-exact-functor-derived-triangulated`.
- `def-weil-triangulated-category`.
- `lem-sf-triangle-morphism-iso`.
- `lem-sf-derived-homology-long-exact`.
- `lem-sf-derived-concentrated-single`.
- `lem-sf-constructible-partition-local-closed-stratum`.
- `lem-sf-proetale-open-closed-sequence`.
- `lem-cbc-proetale-extension-zero-comparison`.
- `lem-weil-pbc-left-exact-injective-resolution-degree-zero`.
- `def-weil-closed-immersion`.
- `lem-weil-pbc-closed-immersion-integral-separated-uc`.
- `lem-weil-pbc-affine-morphism-permanence`.
- `lem-sp-grothendieck-enough-injectives`.
- `lem-weil-pbc-immersion-base-change-lft`.
- `def-weil-constructible-subset`.

No Mathlib/source-library theorem is re-proved here. No unused private import is retained in
the new encoding module. The generic module-sheafification APIs and filtered-colimit preservation
are reused directly.

## Where the brief, the DAG or earlier work was wrong

No false original statement or definition was found. The original detailed derived/recollement
plan is longer than needed because the source library already states and proves the
fixed-module constructible-origin theorem. The missing work is the actual equivalence of
coefficient encodings, including canonical pullback, positive global strata and scalar action;
this delivery proves all of it. The two coefficient encodings are not silently identified.

## New nodes

`lem-weil-pbc-proetale-constant-module-encoding` records the proved equivalence. Its module
also supplies `proEtaleModuleScalarUnit`, `proEtaleModuleRestriction`, and
`proEtaleModuleEncoding`, all constructed from the canonical unit and proved categorical APIs.
Source: Modules on Sites, Tags 03CY and 093I.

`lem-weil-pbc-proetale-constant-module-pullback-encoding` records the proved canonical
pullback identification. Its finite coefficient isomorphism is the finite-level clause of the
existing profinite coefficient comparison. The direct-image comparison is pointwise identity;
uniqueness of left adjoints then gives the required tensor-pullback comparison.
Source: Modules on Sites, Tag 03D3, and the existing finite coefficient comparison.

`lem-weil-pbc-proetale-constant-module-constructibility` records the proved compatibility
of local constancy, finite stalks, and global finite partitions. It reuses the existing
finite-model local-constancy, finite-stalk, and lisse-to-finite-model theorems.
Source: Modules on Sites, Tags 03CY and 093I; Pro-etale Cohomology, Tags 099Y and 09AK.

All three nodes are fully proved in this delivery; none is a remaining obligation. Their
Mathlib searches were run through `msearch.py` and are recorded in `searches.jsonl`.
No change records.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
