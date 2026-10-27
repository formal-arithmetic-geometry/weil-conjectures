## What changed

Decomposed `WeilConjectures.condensedE_realization` into two independent mathematical
obligations: construction of the normalized realization system for individual morphisms,
and comparison of the ordered completed exchange for a supplied normalized system.
The target combines them by existential elimination and application. Its statement is unchanged.

Moved the existing public records and their proved coefficient-transport helper into
`CondensedERealizationDefinitions`; the item publicly reexports that module. Their names,
signatures, attributes and bodies are retained, with explicit (definitionally equal)
return types and map endpoints, plus local interface settings for derived categories and
completed operations. This avoids an import cycle:
the two new statement modules must use the records before the item imports their theorems.
This is a dependency reorganization for the mathematical decomposition, not a split of a
slow proof. The original existence proof remains the only original hole.

No adopted source-library file is changed. The exploratory lower-level route and its
new modules were not delivered; it exposed expensive category-instance conversions but
did not produce a verified assembly.

## Proved and sorry left

Closed the one original hole `WeilConjectures.condensedE_realization` by combining the
two new intermediate statements. This is a decomposition, not a net closure proof:
one hole closed, two holes added, net minus one. The item has zero literal `sorry`.

Every remaining hole in the packet:

- `WeilConjectures.condensedE_realization_system`, node
  `lem-weil-pbc-condensed-e-system`: normalized scalar equivalences and all individual
  functor, adjunction, composition and identity comparisons, without exchange.
- `WeilConjectures.condensedE_realization_system_exchange`, node
  `lem-weil-pbc-condensed-e-system-exchange`: ordered-square exchange for an arbitrary
  supplied normalized system, without asserting that such a system exists.

Each theorem has a complete source-based proof in words. Neither has the same conclusion
as the target. No hole occurs in a definition, instance, or private declaration. The
original proved coefficient-transport adjunction and its helpers are retained.

## No longer needed

The target now uses the two grouped comparison obligations. The full scalar, compactness,
lattice, open-closed and strict-tower arguments belong to those respective obligations;
none is claimed to be globally unnecessary or withdrawn. No source declaration or unit
route is removed.

The definitions module removes these direct proof imports because its retained proved
helper uses coefficient-isomorphism transport, while the new existence and exchange
statements contain their own remaining proof obligations:

- `Sheaf.Paper.AdicCoefficientDatum`.
- `Sheaf.Paper.CondensedPointBasisEvaluation`.
- `Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover`.
- `Sheaf.Paper.ProfinitePointPullback`.
- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`.
- `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`.
- `Mathlib.CategoryTheory.Triangulated.Triangulated`.
- `Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness`.
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.Paper.LisseEConstructibleIntegralLattice`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.
- `Mathlib.Topology.NoetherianSpace`.
- `Mathlib.AlgebraicGeometry.Properties`.
- `Mathlib.Topology.KrullDimension`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `Sheaf.Paper.PbcActualStrictPullback`.
- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`.
- `Sheaf.Paper.SfIntegralDirectImageConstructible`.
- `Sheaf.Paper.SfDerivedDirectImage`.
- `Sheaf.Paper.SfIntegralConstructible`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`.
- `Sheaf.Paper.CompletedDirectImageLimits`.
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`.
- `Sheaf.Paper.StrictTowerExchangeMateNormalization`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`.
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `Sheaf.CategoryTheory.DirectedTriangulatedImage`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`.
- `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`.
- `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom`.
- `Sheaf.Paper.ContinuousCoefficientRealizations`.
- `Sheaf.Paper.ContinuousIntegralCoefficients`.
- `Sheaf.Paper.ContinuousIntegralLocalizationContinuity`.
- `Sheaf.Paper.ContinuousModuleEncodingScalarExtension`.
- `Sheaf.Paper.FiniteModelStratumFiltration`.
- `Sheaf.Paper.PbcQbarCompletedPullback`.
- `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`.
- `WeilConjectures.ConstructibleSheaf.Pullback`.

## Where the brief, the DAG or earlier work was wrong

The original single existence statement combines two separate arguments: the normalized
individual-operation realization, which requires no square, and the additional equality
of the specified ordered completed exchange with the adjunction mate. The latter is an
additional comparison obligation in the node's source record. They are now separate
statements, and no change to the mathematical target or coefficient universes is made.

## New nodes

- `def-weil-pbc-condensed-e-realization-records` attaches the unchanged shared records
  to their definitions module. It asserts no existence and introduces no new choice.
- `lem-weil-pbc-condensed-e-system` records the individual-operation realization argument.
- `lem-weil-pbc-condensed-e-system-exchange` records the ordered-exchange argument for a
  given system. Its integral natural transformation is forced by full faithfulness and
  its ambient normalization; its rational and condensed equations compare actual arrows.

The shared definitions compiled successfully with the original proved adjunction helper
retained. Explicit return types and synchronous elaboration reduce repeated inference;
the delivery performs the final checks of all four modules.

The public reexport is recorded in
`coord/changes/condensed-e-realization-records.md`.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
