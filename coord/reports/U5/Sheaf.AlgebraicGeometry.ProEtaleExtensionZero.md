## What changed

The parent theorem `AlgebraicGeometry.ProEtale.proEtale_extension_by_zero` now combines
existing exactness and adjunction instances with a complete inside-open stalk proof, a
complete proof that its specified scalar mate is invertible, and the outside-open sheaf
vanishing statement in the new module `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroOutsideStalk`.

For the inside case, the fully faithful inclusion of pointed neighbourhoods over U into
those over X is initial: fibre product with U refines every neighbourhood. Its opposite
is final, and `Final.colimIso` gives a natural stalk comparison. The invertible unit of
extension/restriction identifies the restricted extension with the original sheaf.
`Functor.mapHomologicalComplexCompIso` provides the comparison on complexes.

For scalars, lift restriction/coextension of scalars to sheaves. The iterated mate theorem
identifies the specified scalar map with the conjugate of an identity square; the
coefficient triangle identity proves the required equality sectionwise. This proves
invertibility of the actual `openExtensionScalarMap`, without finiteness assumptions.
`NatIso.mapHomologicalComplex` supplies its degreewise isomorphism.

All original public signatures, definitions, and public imports are unchanged. The new
helper uses the existing raw geometric module stalk definition, avoiding an import cycle.
The parent node records the actual route. There are no definition or interface repairs.

## Proved and sorry left

- Closed the original hole in
  `AlgebraicGeometry.ProEtale.proEtale_extension_by_zero`
  (node `lem-cbc-proetale-extension-zero`). Its combination proof establishes all
  exactness, adjunction, inside/outside stalk and specified scalar-mate clauses.
- Proved the new helper `AlgebraicGeometry.ProEtale.openExtension_outside_stalk`
  (node `lem-cbc-proetale-extension-zero-outside-stalk`). The source-library
  local-vanishing theorem kills a section on a weakly etale refinement. A section
  over the algebraically closed geometric point makes it a pointed refinement;
  the colimit relation then kills the germ.
- Original holes: 1. Holes closed: 1. Holes added: 0. No `sorry` remains in either
  delivered module, and no definition or private declaration contains a hole.
- Validation: both modules compile against the current library. Explicit `#print axioms`
  for the parent and outside-stalk helper lists exactly `propext`, `Classical.choice`,
  and `Quot.sound`. Delivery preflight is pending in the shared queue.
  The import-direction check permits the new parent-to-helper import.

## No longer needed

Removed proof imports from the original item:

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleSheafificationGeometricStalk`
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `Mathlib.Algebra.Category.Ring.Limits`
- `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`

The parent proof no longer requires the weakly-etale localization theorem,
`lem-weil-proetale-weakly-etale-localization`, or localized ringed-module exactness,
`lem-pur-site-restriction-module-adjunction-exact`: the concrete source-library
extension/restriction adjunction and exactness instances already suffice.
`def-weil-abstract-derived-category` is not needed for the stated cochain-complex
conclusion. The scalar proof does not require
`def-weil-presheaf-modules-sheafification`: the restriction/coextension adjunction and
iterated mates prove the precise normalization directly. The geometric-stalk sheafification theorem,
`lem-cbc-proetale-sheafification-geometric-stalk`, is also unnecessary for both
proofs: the source-library local-vanishing theorem already works on sheaf sections.
Statement dependencies remain attached to the parent. The top-level obsolete
`tool_uses` approvals for the localization and localized-module exactness lemmas
are removed; no approval is added.

## Where the brief, the DAG or earlier work was wrong

The retained attempt had isolated all three stalk/scalar clauses into one helper in the
parent module and had not updated the parent DAG route. The current reduction proves
inside stalks and scalars directly, isolates just outside vanishing in a separate module,
and updates the route. The resumed work closes that last helper from source-library
local vanishing and weakly etale sections. The retained report was stale: it described
the helper as still holed although its Lean proof had already been started. The unit
record has no realized steps to bypass.

The upstream `Open.Stalk` module describes pullback along a geometric point, whereas this
item uses the pointed-neighbourhood colimit. Reusing that theorem alone would not prove
the displayed statement without a further stalk/pullback comparison. The direct initial
neighbourhood argument proves the inside case for the required colimit.

The new outside-only assertion was checked on the empty open, identity open, and zero
coefficient ring: it respectively asserts the expected zero extension, has an impossible
nonfactorization hypothesis, and takes values in the zero module category.

## New nodes

`lem-cbc-proetale-extension-zero-outside-stalk` states only the outside-open vanishing
for module sheaves. Its Lean declaration is
`AlgebraicGeometry.ProEtale.openExtension_outside_stalk` in the new module
`Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroOutsideStalk`. This helper is proved
completely, using the existing local-vanishing and weakly etale section theorems;
it has no remaining obligation. No existing statement or definition changed;
no change record is required.

`lem-cbc-proetale-extension-zero-local-vanishing` attaches the existing proved
source-library theorem
`AlgebraicGeometry.ProEtale.exists_map_eq_zero_openImmersionLowerShriek`, in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.LocalVanishing`.
It records the local-vanishing input used by the outside-stalk helper; no duplicate
Lean declaration and no hole is introduced.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
