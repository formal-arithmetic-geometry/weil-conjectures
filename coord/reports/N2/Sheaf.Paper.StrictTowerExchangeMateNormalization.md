## What changed

The unchanged statement `AlgebraicGeometry.Scheme.strictTowerExchangeMateNormalization` is proved from the inverse-image cubes and the normalized adjunction-mate calculus. The finite rectangle, ordinary restriction square, exact localization comparison, and general mate cube are proved in five new modules. Completed reduction inverse-image coherence is isolated in a sixth module. The three clauses of the item are combined by explicit corner transports, naturality and the mate cube; no faithfulness of derived evaluation is used.

The scalar-restriction and derived-unit expressions share generic constructions to avoid repeated unfolding of completed coefficient transports. Their components and normalization equation are unchanged; see the change records. All adopted source-library modules retain their declarations and bodies.

Validation: `lcompile.py --all` compiled the seven-module packet without warnings. The five unchanged downstream consumers (`CompletedProjectionCoherence`, `CompletedPullbackUnitTower`, `CompletedTowerCompatibility`, `ProEtaleConstantReductionTower`, `QuotientCornerFrobeniusStructures`) also compiled against the new item. Their temporary test copies are not part of the delivery.

## Proved and sorry left

Closed the item's one original hole: `AlgebraicGeometry.Scheme.strictTowerExchangeMateNormalization`.

Added one remaining hole: `AlgebraicGeometry.Scheme.completedReductionPullback_square`, node `lem-weil-pbc-completed-reduction-pullback-square`. It states only coherence of the normalized inverse-image comparisons, before any mate, projection formula, four-corner evaluation, properness, completeness or witness argument. Its docstring gives the complete K-flat representative argument and its node records the required inputs. This is a decomposition, with one hole closed and one added (net zero), rather than an axiom-free proof of the item.

The following new public theorems have complete Lean proofs: `CategoryTheory.exchangeMate_cube`, `AlgebraicGeometry.Scheme.proEtaleRingRestriction_square`, `AlgebraicGeometry.Scheme.StrictTowerRingedSquare.ambientSquare_localization`, `AlgebraicGeometry.Scheme.finiteReductionPullback_square`, and `AlgebraicGeometry.Scheme.finiteReductionExchange_rectangle`. All private helpers are proved; all definitions construct their data without holes. There are no other added `sorry`s.

## No longer needed

No module is withdrawn. No original import of the item is removed. The proof works directly with the strict functor categories and the already normalized reduction/pullback adjunctions. It does not need the planned diagram-site realization, diagonal K-injective argument, or the broad tensor-exchange coherence presentation. Their ordinary composition and normalized mate consequences are supplied explicitly by the new proofs.

The following former direct proof dependencies are removed from this node's route (they may remain needed by other consumers):

- `lem-weil-pbc-diagram-site-realization`.
- `lem-pc-kflat-resolution`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `lem-weil-pbc-site-derived-tensor-descent`.
- `lem-weil-pbc-small-module-diagrams-grothendieck`.
- `lem-weil-pbc-kinjective-functorial-existence`.
- `lem-weil-pbc-right-adjoint-preserves-kinjective`.
- `lem-weil-pbc-kinjective-total-derived`.
- `lem-weil-tower-category-levelwise-abelian`.
- `def-weil-pbc-adic-coefficient-datum`.
- `def-weil-pbc-adjunction-mate`.
- `def-weil-pbc-projection-formula-map`.
- `def-weil-pbc-four-arrows`.
- `lemma-weil-pbc-perfect-projection-formula`.
- `lem-weil-pbc-finite-level-rectangle`.
- `lem-weil-pbc-ring-sheaf-change-adjunction`.
- `lem-weil-pbc-ringed-exchange-tensor-coherence`.
- `lem-weil-pbc-constant-completion-equivalence`.
- `lem-weil-pbc-profinite-coefficient-inverse-image`.
- `lem-weil-pbc-flat-ringed-diagram-restriction`.
- `lem-weil-pbc-proetale-derived-pullback-composition`.

The parent's approved generic `lem-pc-kflat-resolution` tool entry is removed: the parent's proof no longer constructs a K-flat resolution. The separate completed inverse-image coherence node records that resolution tool in its own proof plan. No global pruning count is claimed.

New proof imports are the mate cube, scalar restriction square, finite rectangle, completed reduction square; the restriction-square module supplies the generic exact-localization cube. The new public MapDerivedCategoryMate import supports the factored public exact-descent definition. The finite and completed mate normalizations are equations in the full functor categories, so the former componentwise evaluation route is not used to identify strict derived morphisms.

## Where the brief, the DAG or earlier work was wrong

The existing `properBaseChangeFiniteLevelRectangle` is stated for `ProEtaleAdicCoefficientDatum` and the `fourArrow...` comparisons. This item uses `AdicCoefficientDatum.chi` and the intrinsic `finiteProjection`. Applying that theorem would require transporting the coefficient categories, completeness datum and chosen normalizations between these interfaces. The proved intrinsic finite rectangle gives the needed equation directly, without properness or completeness hypotheses and without an additional hole.

The broad diagram-site/tensor argument is unnecessary for the finite rectangle and scalar-restriction comparison. Existing normalized adjunction and exact-localization declarations give a smaller route. The remaining completed comparison does require an inverse-image coherence theorem; the given normalized comparison existence theorem does not state that square. It is recorded separately rather than assuming derived evaluations are faithful.

Concrete specialization of object-level cube proofs repeatedly unfolds large coefficient transports during kernel checking. Natural-transformation-level inputs and outputs, plus shared unit-normalization definitions, avoid that repeated work without changing the mathematics.

## New nodes

`lem-weil-pbc-exchange-mate-cube` is realized in `lean/Sheaf/CategoryTheory/ExchangeMateCube.lean`. The statement and proof are supplied; it has no new holes.

`lem-weil-pbc-ring-restriction-pullback-square` is realized in `lean/Sheaf/AlgebraicGeometry/ProEtaleRingRestrictionSquare.lean`. The statement and proof are supplied; it has no new holes.

`lem-weil-pbc-ringed-square-localization` is realized in `lean/Sheaf/AlgebraicGeometry/ProEtaleRingedSquareLocalization.lean`. The statement and proof are supplied; it has no new holes.

`lem-weil-pbc-finite-reduction-pullback-square` is realized in `lean/Sheaf/Paper/FiniteReductionPullbackSquare.lean`. The statement and proof are supplied; it has no new holes.

`lem-weil-pbc-intrinsic-finite-exchange-rectangle` is realized in `lean/Sheaf/Paper/FiniteReductionExchangeRectangle.lean`. The statement and proof are supplied; it has no new holes.

`lem-weil-pbc-completed-reduction-pullback-square` is realized in `lean/Sheaf/Paper/CompletedReductionPullbackSquare.lean`. This is the one remaining completed inverse-image coherence result, strictly below the item.

Change records: `coord/changes/strict-tower-exchangeModuleResPull.md`, `coord/changes/strict-tower-exchangeResPull.md`, `coord/changes/strict-tower-ExchangeResPushNormalized.md`.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
