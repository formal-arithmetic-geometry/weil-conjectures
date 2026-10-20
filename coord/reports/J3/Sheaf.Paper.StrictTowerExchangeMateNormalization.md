## What changed

Closed `AlgebraicGeometry.Scheme.exchangeResPush_existsUnique` in
`Sheaf.Paper.StrictTowerExchangeMateNormalization`.

A proved private categorical lemma constructs the derived adjunction mate from the
ordinary restriction comparison. The library's proved derived-mate factorization gives
its normalization on every complex. Exact scalar extension along the completed constant
algebra is left adjoint to restriction, so termwise restriction preserves K-injectives.
The normalization then makes the mate invertible on K-injective representatives.
Uniqueness follows from the universal property of the right-derived functor.

The flatness and ordinary adjunction are taken from the existing independent-universe
completed-algebra and coefficient-adjunction declarations. All helpers introduced here
are proved; none introduces a new hole.

Added `exchangeWhiskerSquareIso` and used it in the two ordinary tower comparison
constructions to fix their functor parenthesization before inserting coefficient data.
The wrapper is exactly `whiskeringRight.mapIso`, so these definitions retain their maps
and are definitionally equal to their old bodies after unfolding it. Its attachment is
the existing normalization node. The change record is
`coord/changes/J3-strict-tower-whiskering-elaboration.md`.

Reused the existing proved private `proEtaleConstantComparison_comp` through a proof-only
`import all`, removing the two duplicated private constant-composition proofs.
Existing public signatures and public imports are unchanged. No source-library file,
target, consumer, or unit realization was changed.

Validation: `lcompile.py --all` compiled the item (36.7 seconds) and unchanged copies
of all five transitive importers: `CompletedTowerCompatibility`,
`ProEtaleConstantReductionTower`, `QuotientCornerFrobeniusStructures`,
`CompletedProjectionCoherence`, and `CompletedPullbackUnitTower`.
Those copies were used only for verification and are absent from the delivery.
Every existing public signature and the ordered public-import list were compared
against the repository source and are unchanged. The final file has no line over
100 characters and no forbidden declaration form.

## Proved and sorry left

- Closed one original hole:
  `AlgebraicGeometry.Scheme.exchangeResPush_existsUnique`.
- Added zero holes and split off zero statements.
- One original hole remains, unchanged:
  `AlgebraicGeometry.Scheme.strictTowerExchangeMateNormalization`
  (`lem-weil-pbc-strict-tower-exchange-mate-normalization`). Its strict tensor/mate
  coherence and finite-evaluation assertions are still the remaining work.
- The item started with two holes and now has one. The private generic mate theorem,
  K-injective preservation lemma, and termwise ordinary mate lemma are complete.

## No longer needed

The following direct proof imports were removed:

- `Sheaf.CategoryTheory.DiagramSiteRealization`
- `Mathlib.Algebra.Category.Grp.FilteredColimits`
- `Mathlib.CategoryTheory.Abelian.FunctorCategory`
- `Mathlib.CategoryTheory.Sites.Limits`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.PerfectProjectionFormula`
- `Sheaf.Paper.FiniteLevelRectangle`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.CategoryTheory.FlatRingedDiagramRestriction`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.FourArrows`
- `Sheaf.Paper.FourCorners`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

No module is withdrawn. Several removed imports remain transitively available through
statement imports, and the open final theorem retains its documented diagram-site and
finite-evaluation plan. These removals assert that the present proof does not use those
direct imports; they do not assert that all such modules are globally unreachable.

`lem-weil-pbc-flat-ringed-diagram-restriction` is unnecessary for the normalized
restriction comparison: exact scalar extension and the termwise adjunction give the
needed K-injective preservation directly. The node's steps 5--7 now describe this route
and use the existing completed-algebra flatness and ordinary coefficient-adjunction nodes.
The unit's own statement and realized steps are preserved.

The duplicated private declarations `exchangeAdjunctCompComparison` and
`exchangeConstantComparisonComp` were removed in favor of the library proof.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The general single-universe diagram-site restriction
interface is more machinery than the existence/uniqueness helper needs, and applying it
to the pro-etale site's two universes would require additional transport. The existing
completed-constant-algebra theorem and independent-universe ordinary adjunction suffice.

Profiling also exposed costly kernel conversion in the old ordinary comparison bodies.
The abstract whiskering wrapper records the same constructions with their intended
parenthesization. Its public introduction is an implementation repair, not a weakening
or a new mathematical assumption. The final strict-normalization theorem remains open;
this delivery closes its separate normalized direct-image comparison helper.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
