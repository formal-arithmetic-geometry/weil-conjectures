## What changed

Proved the seven ordinary-pullback construction theorems in the original item module.
All existing declaration signatures, public imports, and non-theorem bodies are
preserved. Added only private proof helpers and private proof imports. No adopted
source-library module changes.

Ring inverse image exists by left Kan extension and sheafification in the independent
coefficient universe. The completed coefficient map is the existing ambient map:
its finite projections determine it uniquely. Module direct image has its existing
universe-correct left adjoint; additivity follows from the additive right adjoint.

For unbounded derived existence, transport the actual module categories to
coefficient-sized AsSmall site presentations. There the ringed-topos K-flat pullback
preserves quasi-isomorphisms between flat-term K-flat resolutions. The resolving-class
criterion supplies a left derived functor. Proved private transport lemmas for right
Kan extensions and category equivalences return it to the specified module categories.
No site universe is identified with the coefficient universe.

The quotient augmentation is transported from the normalized ambient strict tower.
Adjunction-unit generators fix each component uniquely. Naturality at consecutive
quotient maps makes its product augmentation vanish after 1-shift; hence the chain-lift
condition holds with zero shifted-product coordinate.

The retained earlier packet extracted the construction and replaced the remaining
locality hole by two new geometric holes. This delivery keeps the seven proved holes
in their original module and keeps the original main theorem unchanged. This leaves
one original hole, introduces zero new holes, and avoids moving 22 public declarations.
The previous construction, assembly proof, proposed split nodes and report are retained
in scratchpad/retained-extraction for further proof work; they are not delivery files.

## Proved and sorry left

Closed seven of the original eight holes, all in
namespace WeilConjectures.IntegralOnSlice:

- ordinaryRingPush_isRightAdjoint
- ordinaryCompletedRingMap_existsUnique
- ordinaryPush_isRightAdjoint
- ordinaryPull_additive
- ordinaryPull_hasLeftDerived
- ordinaryQuotientAugmentation_existsUnique
- ordinaryCompletionChain_condition

One original hole remains: WeilConjectures.IntegralOnSlice.qcqsCompletionUnitLocality,
node lem-fix-qcqs-completion-unit-locality. Its statement, complete proof plan and
sorry body remain unchanged. No holes are added, and none are split off in the delivered
packet. Net direct-hole reduction: seven. All private helpers are proved; no definition
contains a sorry. Existing named dependencies may themselves still contain sorry, as
allowed by stage 3.

The earlier four-module packet compiled successfully against the current server build.
The final single-module packet is checked again by lcompile.py and deliver3.py.

## No longer needed

No module or DAG node is withdrawn. In particular, the geometric dependencies of the
unfinished main theorem remain in its existing DAG proof plan and are still needed.
The proposed construction/restriction/tree split is not introduced into the library.

The following old private proof imports are unused by the seven completed proofs and
removed from the item; they may be needed when its main proof is completed:

- Sheaf.Paper.ExactProductFunctorStrictLimit
- Sheaf.CategoryTheory.LocalizedModuleExactForSystems
- Sheaf.SixFunctors.OpenQuotientKoszulCompleteness
- Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus
- Mathlib.CategoryTheory.Sites.LocalProperties
- Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
- Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
- Sheaf.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
- Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
- Sheaf.Paper.ReductionPullbackDerivedTower
- Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
- Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
- Sheaf.Paper.KoszulReconstruction
- Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap

These import removals are not claims of global mathematical pruning. Public imports
are unchanged. No source-library declaration is removed or returned to sorry.

## Where the brief, the DAG or earlier work was wrong

The original geometric plan uses several declarations whose coefficient size is tied
to site size plus one. The item permits independent site and coefficient universes.
The seven construction proofs handle that mismatch using actual site equivalences and
right Kan-extension transport. The main geometric comparison is still unfinished.
No statement is disputed and no hypothesis is added.

The preceding attempt reported server Git unpack failure during delivery push.
On this resumed attempt, the required initial deliver3.py invocation instead reported
that the retained two-hole split packet was at 0 of 120 reference minutes, with a
72-minute split gate. This confirms that its reference clock was reset on resumption.
The inherited packet identifies searches at 2026-10-24T07:06:09Z through 09:53:22Z;
the resumed mandatory check ran after 10:28Z. No budget or launcher file was changed.
The final packet has no new holes and retains the original top-level obligation.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
