## What changed

Proved `AlgebraicGeometry.Etale.clopenSectionDirectImage` with its signature and canonical-map equation unchanged. Added one proved private categorical helper, `exact_derived_counit_isIso`, which shows that an exact right adjoint with invertible counit has invertible bounded-below derived counit.

The shorter route uses the already proved clopen comparison `isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range`. It identifies extension by zero with exact direct image. The derived direct image along the section is fully faithful; its unit is therefore invertible on the image of derived extension by zero. Push this unit through `Rp_*`, compose the existing derived composition and identity isomorphisms, and cancel the exact derived extension/restriction unit. This produces exactly the map required in the statement, with naturality built into the construction.

Added proof-only imports `WeilConjectures.SixFunctors.Etale.LowerShriek.Proper` and `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact`. Updated the theorem's proof docstring and its existing node's proof, proof_deps and proof_origin; removed two obsolete tool approvals. No definitions, public signatures, public imports, consumers, or target statements changed. The unit has empty realized statement/steps, so no fixed unit route is bypassed.

Validation: launcher single-file compilation passes without errors or warnings (about six seconds). `#print axioms AlgebraicGeometry.Etale.clopenSectionDirectImage` reports exactly `propext`, `Classical.choice`, `Quot.sound`. The temporary print command was then removed. Empty schemes, an identity section, and the zero coefficient ring require no extra hypothesis: the same adjunction identities apply.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Etale.clopenSectionDirectImage` (node `lem-weil-pbc-clopen-section-direct-image`). Added zero holes; split off zero statements. No sorry remains in the delivered module. The private helper `exact_derived_counit_isIso` is fully proved. This is a proof, not a decomposition.

## No longer needed

Removed these six proof-only imports:

- `Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct`.
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`.
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves` (the Mathlib injective-preservation theorem is already visible through the statement's imports).
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (its declarations remain available through the existing public statement imports).

The proof no longer needs these declared dependencies:

- `lem-weil-pbc-etale-sheaf-clopen-product`: the proved clopen shriek/star comparison works directly with module coefficients; no separate abelian product equivalence or scalar-action transport is needed.
- `lem-weil-pbc-module-sheaves-enough-injectives`: the coefficient sheaf category already has the generic proved Grothendieck/enough-injectives instances used by the existing derived API. The imported statement also concerned a different module encoding.
- `lem-weil-pbc-dplus-injective-representative`: the derived adjunction and exact-functor API already perform the resolution argument; the private helper only needs essential surjectivity of localization.
- `lem-weil-pbc-kinjective-hom-derived`: naturality comes from whiskered natural transformations; no morphism-by-morphism K-injective lifting is necessary.
- `lem-weil-pbc-etale-inverse-image-restriction`: no explicit section evaluation is needed.
- `def-weil-open-immersion` and `def-weil-pbc-direct-image` are not separate proof dependencies, but remain statement dependencies through the unchanged statement.

Removed obsolete top-level tool approvals `lem-weil-pbc-etale-sheaf-clopen-product` and `lem-weil-pbc-module-sheaves-enough-injectives`. Kept the extension-by-zero adjunction and exactness approvals. The generic right-derived computation and right-adjoint injective-preservation dependencies remain used. No library files are withdrawn: other parents may still need them.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The DAG's proposed proof did not account for the already proved source-library clopen shriek/star comparison and consequently planned unnecessary scalar-action transport and explicit K-injective representative comparisons. Reusing that comparison and the exact derived-adjunction API proves the full canonical equation directly. The current blueprint snapshot has the same statement and component proof under `sec-proetale-coefficients/sk-def-sf-operations`; the older node's source location is historical. No process or tool defect was encountered.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
