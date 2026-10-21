## What changed

Proved `CategoryTheory.directImageRoosNormalization` using the supplied normalized
units and comparison. Private proved helpers construct the sign-normalized cone
comparison and the Roos triangles by localization. The canonical derived
adjunction supplies product preservation and the unit-compatible shift structure.
Product projections prove the transition and difference squares. The ordinary
limit legs and the comparison-unit equation prove the first outer square.

For the connecting square, products and cones of the evaluated K-injective
complexes remain K-injective. The normalized units make the mapped ordinary-limit
inclusion invertible. The existing additive Roos comparison preserves that
inclusion and the boundary with coordinates `(z, 0)`. Cancellation identifies its
cone map with precisely `d.comparison`. The boundary-model and shift equations
then prove the connecting square on K-injective towers; naturality and functorial
K-injective resolutions extend both outer squares to every derived tower.

Existing public declarations, definitions, signatures and public imports are
unchanged. Only private proved helpers and proof imports were added. The node's
`proof`, `proof_deps` and `proof_origin` record the implemented route. No target,
source-tree declaration, definition interface or consumer was changed. No new
module or node was introduced. The proof-support command record is
`coord/changes/J4-direct-image-roos-proof-support.md`. Local caches of existing
countable-limit instances are confined to private proof sections and the final theorem proof. Four private
isomorphism constructions are irreducible, with explicit proved equations, to
avoid repeatedly expanding them during elaboration. These changes do not enter
public definitions or signatures.

Validation: `lcompile.py` checked the final file together with the unmodified
delivery axiom probe in 50.8 seconds. All 81 declarations passed the axiom probe;
the file has no warnings. The delivery tool checks the final packet independently.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.directImageRoosNormalization`.

There are zero holes left in the item, zero holes added and zero split off.
Every private helper is proved. The proof uses existing declared dependencies;
no axiom was introduced.

## No longer needed

The implemented route does not use these planned proof dependencies:

- `lem-weil-pbc-exact-adjoint-tower-models` and
  `lem-weil-pbc-kinjective-fiber-triangle-comparison`: these statement-only nodes
  were added by a concurrent DAG re-split during this session. The complete Lean
  proof instead uses the smaller existing declarations and proved private
  calculations described above. Neither new node realizes a unit-route step.

- `def-sp-injective-resolutions`: no separate injective-degree computation of the
  target tower is needed.
- `lem-pur-kinjective-degreewise-existence`: functorial K-injective replacement
  suffices; its degree terms need not be injective. The existing
  `lem-weil-pbc-kinjective-functorial-existence` supplies exactly the four
  resolution declarations used.
- `lem-weil-pbc-hom-into-triangle-exact`: Mathlib's closure of a right orthogonal
  under distinguished triangles proves the required cone K-injectivity directly.
- `lem-weil-pbc-small-module-diagrams-grothendieck`: a private separator and
  evaluation-adjunction argument proves the generic tower category Grothendieck.
- `lem-weil-tower-category-levelwise-abelian`: no separate exactness or injective
  preservation argument for the termwise target tower is needed.

Removed the earlier sandbox's unused direct proof imports:
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`,
`Sheaf.CategoryTheory.KInjectiveTotalDerived`,
`Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck`,
`Mathlib.CategoryTheory.Preadditive.Injective.Basic`, and
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`.
The last is replaced by its base module `KInjectiveResolution`.

No global module withdrawal is claimed. Other consumers or transitive imports
can still require those modules. The parent
`CompletedDirectImageLimits.directImageRlim_roos` still needs this item and its
connecting square. The blueprint unit's route is retained. In particular, the
private import of
`Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison` is retained even
though the supplied data already packages its comparison and normalization.

## Where the brief, the DAG or earlier work was wrong

The proof does not require a K-injective model of the termwise target tower.
Normalization of its cone comparison on every complex and naturality of its
projection and boundary suffice. Degreewise injectivity of the source resolution
is also unnecessary.

The current node's review and split-report metadata were refreshed from the
concurrent DAG re-split; only our implemented proof fields are changed.

The earlier attempt's import-resolution failure was not reproduced. The current
compile service resolved the project imports and provided compiler feedback.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
