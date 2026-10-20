## What changed

Proved `AlgebraicGeometry.Etale.ordinary_supported_kummer_uniqueBoundary` from a separately proved unique-boundary theorem. The original signatures are unchanged. The main existence theorem remains untouched with its original sorry.

The new theorem establishes both directions of the equivalence between `SupportedKummerBoundary` and the existing Cartier reduction specification. It then applies `cartierReduction_existsUnique`; pole-boundary uniqueness identifies the relative extension used in the specification. No data definition or target statement changes.

## Proved and sorry left

Closed one of the two original holes: `AlgebraicGeometry.Etale.ordinary_supported_kummer_uniqueBoundary`.

The one remaining hole is `AlgebraicGeometry.Etale.ordinary_supported_kummer`
(node `lem-asd-ordinary-supported-kummer`). No hole is added. The new theorem `AlgebraicGeometry.Etale.supported_cartier_boundary_existsUnique` is proved, including its two-way boundary comparison. No private declaration or definition has a sorry.

The retained full-construction experiments are outside the delivered Lean directory. Their Chern, pullback and scalar obligations are not delivered as new holes and are not claimed proved.

## No longer needed

The unique-boundary proof no longer depends on projecting the main theorem's Chern, pullback, scalar and derived-arrow witnesses. It needs only Cartier reduction and pole-boundary uniqueness through `Sheaf.AlgebraicGeometry.CartierReductionSiteComparison`.

All original private proof imports of the item are removed: the main proof remains the original sorry and the unique-boundary proof uses only `SupportedCartierBoundaryExistence`. The original main node's geometric proof dependencies remain its plan and are not claimed globally pruned.

Removed private imports:

- Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
- Mathlib.Algebra.Homology.Embedding.ExtendHomology
- Mathlib.Algebra.Homology.HomologySequence
- Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
- Mathlib.CategoryTheory.Linear.FunctorCategory
- Mathlib.CategoryTheory.Linear.Yoneda
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
- Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
- Sheaf.AlgebraicGeometry.ClosedSupportHom
- Sheaf.AlgebraicGeometry.DerivedCategories
- Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
- Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget
- Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
- Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
- Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
- Sheaf.AlgebraicGeometry.PullbackConstantModule
- Sheaf.AlgebraicGeometry.RelativeTorsorCohomology
- Sheaf.AlgebraicGeometry.SupportedKummerCartierPullback
- Sheaf.AlgebraicGeometry.SupportedKummerScalarSource
- Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality
- Sheaf.CategoryTheory.RingedSiteModules
- Sheaf.CategoryTheory.Sites.TorsorWithSection
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
- WeilConjectures.AlgebraicGeometry.EffectiveCartier
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
- WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
- WeilConjectures.AlgebraicGeometry.EtaleSheaves
- WeilConjectures.AlgebraicGeometry.Sites.GmPicard
- WeilConjectures.AlgebraicGeometry.Sites.Kummer
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
- WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
- WeilConjectures.SixFunctors.Finite.Exact
- WeilConjectures.SixFunctors.Finite.Stalk
- WeilConjectures.SixFunctors.OpenClosed.Exact

No module is withdrawn. The main node retains its original proof plan and records the new independent proof of its unique-boundary auxiliary theorem.

Validation: both delivered modules compiled in import order with exit code zero and no warnings (`scratchpad/verified-boundary-packet.log`, 41.1 and 36.0 seconds). An additional check retaining all original imports passed in 1.1 and 30.0 seconds (`scratchpad/verified-full-interface.log`). Both original theorem signatures and the original main sorry are retained.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox report claimed unverified full assembly and a shared definition adaptation. Neither is delivered. Profiling isolated expensive kernel normalization in both compatibility clauses; their full proof experiments remain in the scratchpad. This packet makes the verified boundary result available without assuming those clauses.

The original unique-boundary docstring describes projection from the main theorem. The new proof establishes its identical statement directly through the existing Cartier reduction specification. The separate result is true for the empty divisor, N=1 and the zero coefficient ring; no regularity or flatness hypothesis is introduced.

## New nodes

`lem-asd-cartier-boundary-existence`, realized by `Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence`: the unique normalized boundary. Its proof dependency is the existing `lem-sp-cartier-reduction-site-comparison`. Its module contains no sorry.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
