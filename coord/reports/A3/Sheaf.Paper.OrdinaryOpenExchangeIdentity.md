## What changed

Replaced the proof hole in `AlgebraicGeometry.Scheme.cbcDatumOrdinaryExchange_identity`
without changing its statement. The proof identifies the chosen derived inverse exchange
using its K-flat counit normalization and uniqueness, then cancels the transport and
identity isomorphisms. Private, proved categorical lemmas establish compatibility of
exact derivation with the identity and perform the final cancellation.

Added `Sheaf.Paper.OrdinaryOpenModuleIdentity`, containing the actual construction
`cbcModulePullId` and the strictly underived normalization step. This step concerns
ordinary module morphisms; it has no derived category, K-flat resolution, derived
transport, or arbitrary derived object. The assembled derivation from this step is
complete Lean code. The original node now records that argument.

The unclaimed dependency `CompletedExtensionZeroComparison` now names its existing
K-flat normalization predicate instead of repeating it inside the existence theorem.
The generic `Functor.DerivedExchangeCounitNormalization` shares the same counit
equation between its concrete specialization and the categorical derivation proof.
The proved API lemma `cbcDerivedInverseExchange_eq` applies the existing uniqueness
without exposing the choice in consumers. Unfolding the predicate recovers the original theorem type; all existing definition
bodies and public imports are verbatim. The change record is
`coord/changes/A3-open-exchange-normalization-predicate.md`.

## Proved and sorry left

Closed the original hole of `AlgebraicGeometry.Scheme.cbcDatumOrdinaryExchange_identity`
by reduction to the underived identity. Added one hole:
`AlgebraicGeometry.Scheme.cbcUnderivedInverseExchange_identity`, in
`Sheaf.Paper.OrdinaryOpenModuleIdentity`, node
`lem-cbc-underived-open-exchange-identity`. Its complete proof in words is in both
its docstring and node. This is a decomposition: one hole closed, one added, net zero;
it is not claimed as a proof independent of the new obligation. No other new holes
are present in the item or new module. The adapted dependency retains all 19 of
its original holes unchanged (zero closed or added there):
`cbcModulePullbackAdjunction_exists`, `cbcCompletedPullbackComparison_naturality`,
`cbcOpenWeaklyEtale`, `cbcSliceFunctor_continuous`, `cbcFiniteSliceMap_exists`,
`cbcCompletedSliceMap_exists`, `cbcOpenShriek_additive`, `cbcOpenShriek_finiteLimits`,
`cbcOpenShriek_finiteColimits`, `cbcOpenSiteFunctor_continuous`,
`cbcFiniteRestrictionMap_exists`, `cbcCompletedRestrictionMap_exists`,
`cbcOpenAdjunction_exists`, `cbcRightExchange_exists`,
`cbcUnderivedInverseExchange_isIso`, `cbcDerivedInverseExchange_exists`,
`cbcDerivedInverseExchange_isIso`, `cbcCompletedExchange_exists`, and
`completedExtensionZeroComparison`. All are in namespace `AlgebraicGeometry.Scheme`
and node `lem-cbc-completed-extension-zero-comparison`.

`cbcModulePullId` is constructed from existing isomorphisms, with no
choice of unconstrained data and no hole in a definition.

## No longer needed

No pre-existing imports or modules are pruned. The proof import `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`
provides the exact-derived identity factorization lemma used in the private proof. The completed extension-by-zero and
ordinary-comparison dependencies are both used. The adic datum node remains a statement
dependency, but is not separately needed as a proof lemma. No unit statement or proof
step is bypassed. No source-library declaration is removed or altered.

## Where the brief, the DAG or earlier work was wrong

The preceding proof outline described both the underived section calculation and its
derivation, but no existing declaration supplied the former identity for the specified
normalized completed adjunctions. The existing derived-exchange uniqueness declaration
supplies the rest once that ordinary-module equality is available. The new split
isolates precisely this missing step; it does not rename the original derived theorem.

Edge cases were checked at the level of the stated argument: empty opens, the zero
module, and unbounded complexes require no extra hypotheses. The section comparison
is functorial pullback identity on every test object, and the derivation uses no
boundedness or quasi-compactness assumptions. No statement dispute was found.

## New nodes

`lem-cbc-underived-open-exchange-identity` records the module-level identity comparison,
with a source in Stacks `lemma-shriek-base-change` and the ringed-site localization
and module-adjunction lemmas. Its steps compare the normalized module adjunctions,
check the right exchange on sections, and transpose using triangle identities.
The new module is `lean/Sheaf/Paper/OrdinaryOpenModuleIdentity.lean`. The node is a
strictly simpler part of the original identity-base-change argument and retains its
unit and blueprint ancestry. The definitionally identical predicate refactor is documented in
`coord/changes/A3-open-exchange-normalization-predicate.md`. No other group's module
was adapted.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
