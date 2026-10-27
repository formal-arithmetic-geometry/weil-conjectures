## What changed

Proved `WeilConjectures.pullbackTensorIntegralPullbackModel_existsUnique`, without
changing its statement. The private naturality proof
`pullbackTensorPullbackTower_naturality` assembles the prescribed finite-level
comparisons into naturality of the strict tower. The private construction
`pullbackTensorReferencePullbackModelIso` composes it with coherent reduction, exact
derived pullback and the Roos comparison; its component lemma is fully proved.

Added the fully proved general categorical theorem
`CategoryTheory.normalizedDescentComponents_existsUnique` in
`Sheaf.Paper.IntegralPullbackDescentComponents`. The item applies it to the existing
normalized descent universal field and the concrete model comparison.

After profiling, conversion refactors and the categorical separation, the combined
item still took 67 seconds. Split its existing 51-declaration construction prefix into
`Sheaf.Paper.CompletedPullbackTowerCore`, re-exported by the item. All existing names,
signatures, construction bodies and normalizations stay the same. Four existing holes
move to that core; no new hole is created. Local transparency attributes affect only
proof elaboration. The unchanged public consumer compiled against the split. The private consumer
needs only one proof import to reach the relocated helper; see Forced adaptations.
The relocation and consumer record is
`coord/changes/N4-completed-pullback-core-split.md`.

## Proved and sorry left

Closed one of the original eleven holes:
`WeilConjectures.pullbackTensorIntegralPullbackModel_existsUnique`.
Added zero holes. The new component theorem and all private comparison helpers are
completely proved. The original integral pullback hole is not replaced by another
statement of the same obligation.

Four existing holes now occur in `Sheaf.Paper.CompletedPullbackTowerCore`, attached to
`def-pur-completed-pullback-tower-core`:

- `WeilConjectures.pullbackTensorReductionModel_existsUnique`
- `WeilConjectures.pullbackTensorReductionEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorRoosModel_existsUnique`
- `WeilConjectures.pullbackTensorPullbackTower_existsUnique`

Six existing holes remain in `Sheaf.Paper.CompletedPullbackTowerRealizations`, attached
to `def-pur-completed-pullback-tower-realizations`:

- `WeilConjectures.pullbackTensorTensorTower_existsUnique`
- `WeilConjectures.pullbackTensorReductionGood`
- `WeilConjectures.pullbackTensorIntegralTensorModel_existsUnique`
- `WeilConjectures.pullbackTensorSequenceCochain_existsUnique`
- `WeilConjectures.pullbackTensorSequenceGood`
- `WeilConjectures.pullbackTensorSystemComparison_existsUnique`

The proof uses the existing reduction, Roos and strict tower declarations with these
remaining holes, as intended by stage 3. The general component theorem is proved from
its stated universal property, which the item supplies from the existing descent record.
Naturality and isomorphism cancellation include zero complexes, zero or identity maps
and empty schemes; no coefficient flatness or boundedness condition is added.

## No longer needed

No mathematical nodes, modules or unit-route steps are pruned. These proof imports
are removed from the item and retained in the extracted core, where their proofs live:

- `Sheaf.Paper.IntegralComparisonSequenceSystems`
- `Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses`
- `Sheaf.CategoryTheory.SequenceModulePullbackEvaluation`
- `Sheaf.Paper.IntegralComparisonSequenceDirectEvaluation`
- `import all Sheaf.Paper.ProEtaleCanonicalTensorPullback`
- `import all Sheaf.AlgebraicGeometry.ProEtaleOperations`

The existing public imports stay. The item adds a public import of its core and a
private import of the proved component lemma. The remaining holes still need the
existing dependencies.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan was correct. Its representative model needed explicit
naturality in the representative, now proved from the prescribed finite-level formulas.
No statement repair or source-library change was needed. Compile-time failures were
handled by profiling, reducing conversion work and then splitting the unchanged
construction prefix, following the brief's step 3a.

## Forced adaptations

`Sheaf.Paper.CompletedPullbackTensorComparison` (holder B4) compiled unchanged against
the split. Its temporary copy was removed after verification.

`Sheaf.SixFunctors.OrdinaryOpenFiniteEvaluation` was unclaimed when adapted. Its original
source failed at line 42 with `Unknown identifier pullbackTensorSequenceRing_eq`,
followed by an unsolved equality in `direct_eq`. The private helper moved with the core.
The sole edit adds `import all Sheaf.Paper.CompletedPullbackTowerCore` immediately after
the existing import-all of the item. Every existing signature, public import, proof and
attribute stays identical. The consumer contains zero holes and compiled successfully after this import change.
The final `lcompile.py --all` run compiled the core, the general component lemma,
the item and the adapted consumer. The public consumer had already compiled unchanged.
The moved prefix was also checked byte for byte against the current shared source,
apart from its blueprint identifiers.

## New nodes

`lem-pur-integral-pullback-descent-components` records the completely proved component
form of a normalized descent universal property in arbitrary categories. The item
supplies the existing `IntegralPullbackDescent.universal` field and its concrete model.

`def-pur-completed-pullback-tower-core` records the unchanged construction prefix
extracted for compilation. Its four holes already existed under the same names; it
adds no new assumption. The original node retains the unit route and delegates the
prefix construction to this node. The change record is
`coord/changes/N4-completed-pullback-core-split.md`.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
