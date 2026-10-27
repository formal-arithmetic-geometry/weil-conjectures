## What changed

Proved `AlgebraicGeometry.Etale.isIso_strictLocalOrdinaryDirectImageComparison`
with its signature and docstring unchanged, following the two steps of its existing node.
Added three private proof imports: `StrictLocalSmallModel.BaseChangeGlobalHomology`,
`BaseChange.DerivedComparison`, and `RightDerivedFunctor.PlusSingleZero` (under their
respective `Sheaf.AlgebraicGeometry` and `WeilConjectures` namespaces).

On the single complex of an abelian sheaf, the generic bounded-below derived mate
factorization and the square comparison identify the derived mate with the
resolution-defined exchange (`mate_eq_derivedExchange`). The resolution factorization
then expresses it through the levelwise ordinary exchange. Left exactness makes both right-derived units invertible on degree-zero
homology; exact inverse image preserves the first identification. The single-complex
homology comparison identifies the intervening levelwise exchange with the ordinary
exchange as an arrow. Mapping this arrow isomorphism through strict-local global
sections transfers the existing strict-local global-homology isomorphism to the goal.

The argument adapts the already proved module-valued degree-zero arrow proof directly
to `AddCommGrpCat`, without requiring an unbounded flat-resolution instance. A proved private helper states the degree-zero arrow comparison for four abstract
additive functors between abelian categories. This keeps scheme inverse/direct-image
definitions out of the expensive homotopy-composition conversion.
Updated the existing node proof text to record the direct mate factorization.
No statement, definition, source-library module, or unit route changes.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.isIso_strictLocalOrdinaryDirectImageComparison`
(node `lem-weil-pbc-strict-local-ordinary-direct-image-comparison`).
No sorry remains in the item. Added 0 holes and split off 0 statements. The proof uses
the existing `smallModel_isIso_strictHenselization_baseChange_globalHomology` and its
recorded dependencies; their remaining obligations are unchanged.

## No longer needed

None. No imports, nodes, modules, or declarations were removed. All three private
proof imports are used. Both steps and all three proof dependencies of the existing
node remain the proof route; no new dependency nodes are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the brief or node was found. The left-exact
injective-resolution degree-zero dependency is a Mathlib leaf; its convenient
bounded-below derived-unit formulation is already proved as
`CategoryTheory.Functor.isIso_homologyFunctor_zero_map_rightDerivedFunctorPlusUnit_app`
in `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingleZero`.
The module-valued theorem cannot be applied
directly to an abelian sheaf, so its category-independent argument was instantiated
here. The generic mate factorization gives the required comparison without the extra
flat-resolution hypotheses of `baseChange_eq_derivedBaseChangeMapPlus`.
The two proved private helpers keep the derived mate equality generic in the square
and the degree-zero arrow calculation generic in its additive functors, avoiding
expensive unfolding of scheme inverse and direct images.

Validation: the complete proof compiled in 36.5 seconds with profiling enabled;
the delivered file removes both temporary profiling options.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
