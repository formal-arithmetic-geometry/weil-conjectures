## What changed

Filled four existing theorem holes in
`Sheaf.Paper.StrictReductionCompactSupportNormalization`, preserving all public
signatures and constructions. Naturality is obtained from the published natural
comparison isomorphisms. Source composition is obtained from the existing scalar
pullback composition statement and compositor naturality. Source and target reduction
identities follow from naturality, functoriality and cancellation of the specified
open/pullback corner. Private categorical helpers contain complete proofs only.
No new public declaration, new module, definition repair, or split-off hole is introduced.
Local irreducibility attributes keep large derived-category constructions out of
routine elaboration; they change no exported definition.

## Proved and sorry left

Original holes: 18. Holes closed: 4. Holes added: 0. Remaining holes: 14.
All listed names are in `AlgebraicGeometry.Scheme.StrictSupportNormalization`.

Closed:

- `kappa_naturality`
- `kappaSource_composition`
- `kappaTarget_reduction`
- `kappaSource_reduction`

Still `sorry`, all attached to
`lem-pur-strict-reduction-compact-support-normalization`:

- `strictReductionCompactSupportNormalization`
- `scalarPull_composition`
- `inputPull_composition`
- `refinement_normalization`
- `refinement_cocycle`
- `targetRefinement_normalization`
- `refinement_exchange`
- `inputPull_identity`
- `refinement_isIso`
- `commonRefinement_normalization`
- `commonRefinement_coherence`
- `scalarPush_composition`
- `sourceRefinement_normalization`
- `kappaTarget_composition`

`kappaSource_composition` uses the pre-existing named `scalarPull_composition`
statement; no new assumption or split-off restatement is introduced.

## No longer needed

Removed redundant direct proof imports (all completed proofs use the already public
comparison APIs):

- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.Paper.CompletedOpenExchangeTransport`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`
- `Sheaf.AlgebraicGeometry.ProEtaleRingRestrictionSquare`
- `Sheaf.CategoryTheory.FlatRingedDiagramRestriction`
- `Sheaf.Paper.RingedOpenStrictReduction`
- `Sheaf.CategoryTheory.RingedOpenScalarAdjunction`
- `Sheaf.Paper.CompletedOpenFiniteTransposeCoherence`
- `Sheaf.Paper.RingedCommonQuotientPullbackComparison`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization`
- `Sheaf.AlgebraicGeometry.ProperOpenClopenProjector`
- `Sheaf.CategoryTheory.ExchangeMateCube`

No module or DAG node is withdrawn. The unproved normalization and composition
clauses still require the original mathematical dependency route. No claim is made
that their dependencies can be pruned merely because the categorical consequences
proved here do not use them directly.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The item has eighteen theorem
holes, and this is a partial proof delivery of its naturality and corner identities.
The main proper/open normalization and the listed coherence inputs remain open.
The unit route and the node's planned mathematical argument are preserved.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
