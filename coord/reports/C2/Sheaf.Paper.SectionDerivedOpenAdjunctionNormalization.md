## What changed

Replaced the single sorry in `sectionDerivedOpenAdjunctionNormalization` with a proof
assembling the ordinary scalar equations, ordinary Hom/unit/counit equations, eight
finite-limit/finite-colimit instances, and derived Hom/unit/counit equations.
All existing declaration signatures and definition bodies are unchanged. The three ordinary
helpers `openSectionObject`, `internalOpenGenerator`, and `openCoefficientSection` move
verbatim into `SectionOpenGeneratorScalar` and remain publicly reexported by the item.
The two localized-adjunction definitions remain in the item. The two nodes' Lean
attachments record this movement.

The ordinary extension comparison is already pinned by its mate in
`InternalModuleOperations.openComparison_existsUnique`. The proof extracts that property
and uses the general mate transpose, unit, and counit identities. For the derived part,
private proved lemmas compute the independent exact-localization units, identify their
adjunctions with the source library's levelwise derived adjunctions by localization
extensionality, and use `Adjunction.mapDerivedCategoryAdjunction_mate`. Expansion of the
fixed pullback comparison then cancels the exact left-derived identification. The Hom
identity applies to arbitrary derived morphisms; no cochain representative is assumed.

The local scalar calculation is isolated in the new ordinary-only module
`Sheaf.Paper.SectionOpenGeneratorScalar`. Only its first scalar equality remains open;
linearity of the already specified comparison proves the second equality. The new
statement is one strict part of the original conjunction and has no derived-category,
comparison, Hom, exactness, unit-normalization, or counit-normalization assertions.

The public imports now name `SectionDerivedRealization`, `ExactDerivedAdjunction`,
and `SectionOpenGeneratorScalar`, which provide the definitions used by the public
signatures. The scalar theorem uses the named generators directly: the original expanded
let-expression statement forced a kernel timeout when compared with these definitions.
Moving the unchanged generator definitions beside it avoids that expansion. No current library
module directly imports the item (checked with a whole-library import search); its DAG
parents and Lean attachment are retained. No existing module besides this item is changed.

## Proved and sorry left

Original holes: 1. Closed upper holes: 1, in
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.sectionDerivedOpenAdjunctionNormalization`.
New holes: 1, in
`AlgebraicGeometry.ProEtale.ModuleRingedComparison.sectionOpenGenerator_scalar`
(node `lem-pd-section-open-generator-scalar`). This is a decomposition with net zero holes,
not a claim of a net proof. The original item contains zero sorry tokens. All private
helpers have complete proofs; no definition contains a sorry.

The new statement has a complete proof in words from Stacks 03DI and the specified
projection-formula action. Its identity-open and empty-open specializations were checked
mathematically in the docstring and node. Both modules compiled through the prescribed remote `lcompile.py --all`: scalar module
5.6 seconds and normalization module 34.7 seconds. The profiling options used to locate
the kernel bottleneck have been removed; `deliver3.py` supplies final compilation,
axiom and packet checks. There are no direct Lean importers to adapt. The theorem
signature and all five existing definition signatures/bodies were compared verbatim
with the source and are unchanged, with the three ordinary definitions relocated as
noted above.

## No longer needed

Removed direct imports:

- `Sheaf.Paper.SectionDerivedPushpullNormalization`
- `Sheaf.SixFunctors.OpenTensorNormalizationData`
- `Sheaf.Topology.ProfiniteCondensedRing`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheafAdjoint`
- `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `Sheaf.CategoryTheory.SheafTensor`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Localization.Adjunction`
- `Mathlib.CategoryTheory.Localization.Predicate`

`SectionDerivedPushpullNormalization` is replaced by its definition dependency
`SectionDerivedRealization`: the fixed pullback comparison is already defined by exact
localization, so the resolution-normalization theorem is unnecessary here.
`OpenTensorNormalizationData` is replaced by `ExactDerivedAdjunction`: no open tensor,
base-change-square, or finite-realization data enter this adjunction proof.

The following former direct proof dependencies are absent from this node's new proof:

- `lem-weil-proetale-weakly-etale-localization`
- `sk-def-sfb-coefficient-morphisms`
- `sk-def-sfb-module-pushforward-pullback`
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`
- `lem-weil-pbc-site-extension-by-zero-presheaf-adjoint`
- `def-weil-extension-by-zero-presheaf`
- `sk-def-sfb-transport`
- `sk-def-sfb-sheaf-tensor`
- `sk-def-sfb-change-of-scalars`
- `def-weil-presheaf-modules-sheafification`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-pe-internal-section-tensor-comparison`
- `lem-pd-section-derived-pushpull-normalization`

The scalar-construction dependencies remain needed by the new scalar node; removing
them from this node does not withdraw them from the library. The separate slice exactness
and the pushpull resolution-normalization arguments are unnecessary for the route above.
No module is withdrawn, and no adopted source declaration or import is removed.
No unit's own statement or proof step is bypassed.

Removed obsolete top-level tool approvals, keeping all retained entries in their original
order:

- `lem-weil-proetale-weakly-etale-localization`
- `sk-def-sfb-coefficient-morphisms`
- `sk-def-sfb-module-pushforward-pullback`
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence`
- `lem-weil-pbc-site-extension-by-zero-presheaf-adjoint`
- `def-weil-extension-by-zero-presheaf`
- `sk-def-sfb-transport`
- `sk-def-sfb-sheaf-tensor`
- `sk-def-sfb-change-of-scalars`
- `def-weil-presheaf-modules-sheafification`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-pe-internal-section-tensor-comparison`

## Where the brief, the DAG or earlier work was wrong

No statement was found false. The original plan repeats ordinary normalization that is
already part of the fixed comparison's defining unique property, and repeats an
identification already present in the definition of `derivedPullComparison`.
The implementation uses those definitions directly. The scalar-generator calculation
still requires matching the internal projection-formula action with the restricted
section action; it is not implied merely by the existence of an arbitrary extension
isomorphism, so it remains a separate genuine proof obligation.

## New nodes

`lem-pd-section-open-generator-scalar`, in
`dag/nodes/sec-poincare-duality/lem-pd-section-open-generator-scalar.json`, states only
semilinearity of the specified ordinary abelian open-unit generator for the actual
coefficient morphism. The source is Stacks 03DI and original Steps 2--3 of the item's
node. Three recorded Mathlib searches and a blueprint-wide search found no matching
statement. The node and theorem give the complete projection-map/pure-tensor argument.
The three unchanged ordinary helper declarations move into this module to keep the scalar
statement in terms of the same named definitions. The original module publicly reexports
them. No existing definition body changes and no other existing module is edited.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
