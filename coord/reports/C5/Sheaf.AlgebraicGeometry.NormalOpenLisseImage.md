## What changed

Proved `AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_lowerStar_of_normal_open`
with its existing signature and visibility unchanged. Added the proved private glue lemma
`mono_generic_transpose` in the same module. No definitions or other modules change.

The proof takes the generic point of X through the open V, trivializes the resulting
constructible field sheaf after a finite separable extension E/k(X), and constructs
Y=X.normalizationIn E. The normal generic-unit theorem identifies the constant sheaf on Y
with the direct image of its constant generic sheaf. Generic injectivity for a locally
constant source gives L -> h_*M; direct-image composition and preservation of monomorphisms
then give k_*L -> nu_*M_Y. Finite pushforward is constructible, and so is its subobject.
The module-valued source-library generic-kernel and finite-pushforward theorems are used
directly, avoiding abelian-forgetful glue.

Updated the item's `proof`, `proof_deps` and `proof_origin` to match this route and withdrew
unused `tool_uses` approvals. The unit record has no realized statement or steps assigned
to the removed auxiliary nodes; no unit-level route is bypassed. The source proof's finite
normalization / constant image / finite pushforward / subobject argument is retained with
one generic field in place of a finite cover and its components.

Added proof-only imports:
- `Sheaf.AlgebraicGeometry.ConstructibleFieldFiniteSeparableConstant`
- `WeilConjectures.ConstructibleSheaf.FiniteMorphism`
- `WeilConjectures.ConstructibleSheaf.FinitePushforward`
- `WeilConjectures.ConstructibleSheaf.Monoidal`

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_lowerStar_of_normal_open`
(node `lem-fin-normal-open-lisse-image`).

Added 0 holes. There are 0 `sorry` declarations left in the delivered module and no new
modules or split-off statements. Imported dependencies retain their own existing proofs
and any existing holes; this delivery does not claim to close those transitively.

## No longer needed

Removed direct imports (a module listed here can still occur transitively through a retained
source-library import):
- `Mathlib.Algebra.Category.ModuleCat.FilteredColimits`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
- `Mathlib.CategoryTheory.Limits.Types.Filtered`
- `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`
- `Sheaf.AlgebraicGeometry.EtaleNormalComponents`
- `Sheaf.AlgebraicGeometry.FiniteNormalClopenConstructibleModule`
- `Sheaf.AlgebraicGeometry.FinitePushforwardFiniteStalkModule`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison`
- `Sheaf.AlgebraicGeometry.LisseTrivializedFiniteEtale`
- `Sheaf.AlgebraicGeometry.NormalConstantOpenImage`
- `Sheaf.AlgebraicGeometry.NormalizationExtendsCover`
- `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues`
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `WeilConjectures.AlgebraicGeometry.IsFiniteTypeEtaleModuleSheaf`
- `WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison`
- `WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension`
- `WeilConjectures.SixFunctors.Finite.Stalk`

Removed direct proof dependencies of this item:
- `def-constructible-constructible`
- `def-weil-pbc-etale-constructible-sheaf`
- `fin2-lem-lisse-trivialized-finite-etale`
- `lem-fin-etale-normal-components`
- `lem-fin-normal-clopen-constructible-module`
- `lem-fin-normal-constant-open-image`
- `lem-fin-normal-underlying-stalk-finite`
- `lem-fin-normalization-extends-cover`
- `lem-galois-finite-stalks-comparison`
- `lem-weil-pbc-etale-morphism-open-map`
- `lem-weil-pbc-finite-closed-map-finite-fibres`
- `lem-weil-pbc-geometric-stalks-detect-mono`
- `lem-weil-pbc-inverse-image-stalk-germ`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lem-weil-pbc-module-abelian-inverse-image-comparison`
- `lem-weil-pbc-noetherian-open-subscheme-noetherian`
- `lem-weil-pbc-normalization-in-residue-field-extension`
- `lemma-weil-pbc-finite-stalk-formula`

The cover-trivialization, component decomposition, cover-extension and finite-product steps
are replaced by generic-field trivialization and one normalization. The module-valued
source-library API handles generic injectivity and finite constructibility directly, so the
separate abelian comparison, finite-stalk formula, filtered-colimit element descriptions,
clopen constructibility, and separably closed stalk comparison steps are unnecessary here.
Global reachability and removal from the queue are for the maintainer to determine.

Withdrew these obsolete top-level tool approvals:
- `lem-fin-etale-normal-components`
- `lem-galois-finite-stalks-comparison`
- `lem-weil-pbc-etale-morphism-open-map`
- `lem-weil-pbc-filtered-colimit-modules-elementwise`
- `lem-weil-pbc-filtered-colimit-sets-elementwise`
- `lem-weil-pbc-finite-closed-map-finite-fibres`
- `lem-weil-pbc-inverse-image-stalk-germ`
- `lem-weil-pbc-locally-noetherian-quasi-separated`
- `lem-weil-pbc-module-abelian-inverse-image-comparison`
- `lem-weil-pbc-normalization-in-residue-field-extension`
- `lemma-weil-pbc-finite-stalk-formula`

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement was found. The DAG's longer route is unnecessary
given the existing generic-field trivialization, generic-kernel, normalization and finite
pushforward APIs. The original module imported several dependencies twice; duplicates were
removed with the unused imports. The declaration's original docstring still records that
historical proof plan; the updated node and this report describe the proof actually written.

The existing normality assumption supplies integrality and nonemptiness of V. The proof
uses these properties; normality is stronger than needed for the generic-kernel argument.
No hypothesis is changed. Field and constant sheaf witnesses are used only within theorem
proofs; the normalization, morphisms and constant sheaves are actual library constructions.
No data-valued definition is obtained from a mere existence theorem.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
