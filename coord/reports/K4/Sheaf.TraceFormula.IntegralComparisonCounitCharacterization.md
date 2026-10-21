## What changed

Filled both original theorem proofs in
Sheaf.TraceFormula.IntegralComparisonCounitCharacterization, without changing any
existing signature or definition. The first proof uses the already constructed
integralComparisonConstantAdjunction and integralComparisonTowerCounit_computes.
The second uses a proved private normalization lemma for arbitrary strict tower
augmentations: transpose theta followed by a K-injective resolution under the ordinary
complex adjunction; identify the two zero-coordinate cone maps; apply the prescribed
Roos normalization and the derived counit formula. Bijectivity gives uniqueness, and
cancellation of the representative isomorphisms gives the specified cone formula.

## Proved and sorry left

Holes closed (2):

- AlgebraicGeometry.ProEtale.integralComparisonLimitCounitCharacterization.
- AlgebraicGeometry.ProEtale.integralComparisonCounitCharacterization.

Holes added: none. Sorries left in the delivered module: none. All private helpers
are proved. This proves the item from its existing library dependencies; it does not
claim that all imported dependencies are themselves free of sorry.

Validation: the remote single-file compiler accepted the final module cleanly in
44.6 seconds, with no warnings and no sorry in the source.

## No longer needed

Removed imports:

- Sheaf.CategoryTheory.StrictRoosComparison (unused public proof-plan import).
- Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral.
- Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact.

The direct invocation of preDerivedAdjunctionGeneral in the old plan is unnecessary:
IntegralComparisonRealizationModels already constructs the required derived adjunction
and proves its K-injective counit formula. The normalized Roos model is an explicit
hypothesis, so no new construction or exact-products theorem needs to be applied here.
The actual zero-coordinate calculation is proved before localization. Removed direct
DAG proof dependencies and their old tool-use entries:
lem-pc-pre-derived-adjoint-functors-general,
lem-weil-proetale-countable-products-exact, and lem-weil-strict-roos-comparison.
Their underlying theory remains available through the existing model APIs; this is
pruning of this proof's direct dependencies, not a claim of global unreachability.
The proved signed-cocone inclusion identity is used as a generic tool.
No module is withdrawn, and no upstream declaration is changed.
The public-import removal is recorded in
coord/changes/K4-integral-counit-unused-roos-import.md; no current module imports
the item. Its DAG parents and unit attachment are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The DAG's first three steps predate the
proved adjunction/counit API in IntegralComparisonRealizationModels and can now be
shortened to that API. The normalization field applies to every K-injective tower,
so the proof does not need to construct a resolution with injective terms. The given
injective-term condition in the first theorem is retained unchanged.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
