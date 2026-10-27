## What changed

Proved `AlgebraicGeometry.ProEtale.qcqs_constructible_integral_lattice_tree` in its
existing module with all six public declarations and their signatures unchanged.
Both rational coefficient cases use a generic assembly proof. Private, fully proved
helpers construct recursive complementary pullback refinements, transport lissity,
handle zero models on empty schemes, and identify scalar modules with finite-dimensional
vector spaces. Actual supplied strata and pulled integral modules are preserved.

The recursive construction specializes the existing proof of
`Sheaf.SixFunctors.ExistsFiniteRefinementTree` before its numerical encoding; it uses
`exists_constructible_cut` from the already imported refinement module. This avoids
converting a numbered tree back to a recursive tree. The scalar proof reuses
`finiteConstantLocalModel_iff_exists_cover`, `models_free_cover`, the internal-module
comparison, and finite-biproduct coordinates from `FiniteConstantLocalModel` via
proof-only `import all`. Lisse transport uses the proved generic `locFree_pullback`
and `locFree_iso` helpers from `FiniteEtaleLocallyFreeModels`, also via `import all`.
Added the proof-only `Mathlib.AlgebraicGeometry.PullbackCarrier` import. Updated the
node's proof, proof dependencies and proof origin to describe this implementation.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.qcqs_constructible_integral_lattice_tree`
(node `lem-sfb-qcqs-constructible-integral-lattice-tree`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
All private helpers are completely proved. The remote `#print axioms` check reports
exactly `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`.
Remote compilation succeeds without warnings (16.3 seconds for the axiom probe), including
empty schemes, zero ranks, varying coefficient fields and arbitrary qcqs schemes.

## No longer needed

Removed direct proof imports `Sheaf.Paper.ContinuousLocallyFreePullback`,
and `Sheaf.AlgebraicGeometry.InternalExtensionInverseImage`.
`Sheaf.Paper.CartesianCoefficients` remains imported as required by the unit route,
although the normalized `pullIso` suffices for the scalar comparison.
The corresponding planned dependencies
`lem-weil-pbc-continuous-locally-free-pullback`,
and `lem-sfb-internal-extension-inverse-image`
and their obsolete top-level tool approvals are removed from this node. They
are not used directly: normalized lisse transport and `CondensedRing.pullIso`
already provide the needed assertions. The separately cited
`sk-def-sfb-coefficient-morphisms` is not needed as a direct proof dependency because
`pullIso` contains its naturality argument. These dependencies may remain required
by other modules, including transitive imports; no declaration or module is withdrawn.
The numerical encoding theorem `lem-fix-scheme-refinement-tree-encoding` and the
numbered-tree conclusion of `lem-fix-constructible-open-closed-refinement-tree` are
not used by this proof. No public import is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The declared refinement theorem
returns a numbered tree, whereas the item uses a recursive tree. The existing proof
already constructs the latter before encoding; reusing that construction avoids a
large reverse conversion. `ContinuousLocallyFreePullback` uses raw inverse-image
coefficient rings, whereas the item uses normalized `IsLisseCoefficientModule`;
the existing normalized lisse helpers fit directly. The canonical `pullIso` also
makes separate reconstruction of internal inverse-image/scalar transport unnecessary.

The new dependencies are existing generic tools: finite scalar-model comparison,
internal modules versus ordinary modules, finite-biproduct coordinates, normalized
lisse pullback/isomorphism transport, and underived Pull. No unit-level realization
is bypassed and no source-library declaration is edited. Edge cases checked in
Lean include the empty cover/empty scheme, zero-dimensional scalar modules, empty
presentation matrices, nonempty leaves and arbitrary supplied stratum structures.

Searches: LeanFinder for finite open/closed lattice refinement returned only general
scheme-cover and affine-transition results; Loogle did not identify the project
internal-module predicate. Repository `rg` located the exact scalar-model comparison,
normalized lisse helpers, existing recursive refinement proof and canonical `pullIso`.
No existing theorem states this item's complete assertion.

The scope-only command additions and removal of unused proof imports are recorded in
`coord/changes/B2-qcqs-lattice-tree-proof-scopes.md`. No public type or definition
body changes. The initial preflight requested this record and retaining the mandated
CartesianCoefficients unit-route import; both requests are addressed.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
