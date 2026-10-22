## What changed

Implemented the eight-step canonical shift and action-unit argument. The given universal
left-derived comparison computes on flat-term K-flat complexes. Two-variable resolving descent
constructs the uniquely normalized tensor comparison. Signed cochain shift compatibility descends
by faithful restriction and resolving essential surjectivity. The cochain action unitors descend
along localization, are unique, and satisfy both pullback unit equations.

Added two proved helper modules: independently sized resolving computation, and compatibility of
the prescribed insertion-of-one cochain comparison with both signed shifts. The latter identifies
the prescribed comparison with the existing additive bifunctor comparison on every totalization
summand. All published tensors, representative comparisons and cochain unitors are preserved.
Transparent presentation names for the existing derived tensor and representative isomorphism keep their data
folded during the proof. The public shift hypotheses retain the original derived tensor; an identity
conversion uses its given shift structure locally, without adding any global instance.
No adopted source-library declaration was edited or removed.

Validation: `lcompile.py --all` compiled the complete assigned module in 55.8 seconds
and the unchanged direct consumer, `Sheaf.Algebra.Homology.ExactPullbackSignedComparison`
(held by X8), in 29.0 seconds. The packet also compiled both proved helper modules, a temporary
importer checking the restored sheaf-composition instance, and an axiom inspection module.
The main theorem and both helpers use only `propext`, `Classical.choice`, and `Quot.sound`,
as confirmed by `#print axioms`. Local irreducibility of the existing fixed cochain shift instances and signed setup keeps their
large definitions folded during elaboration. The lower-level complex and bicomplex mapping
constructors are also kept folded. The public helper bodies use the definitionally equal
derived-tensor presentation. A separate importer checks the original predicate equivalences and both directions of the action-unit interface.
The final delivery tool repeats the required compilation and preflight checks.

## Proved and sorry left

Original holes: one, in
`SheafOfModules.PullbackTensorCanonical.pullback_tensor_canonical_shift_unit`.
Closed that hole with a complete proof from the stated dependencies. The retained implementation
contains zero `sorry`s. The complete main module and its unchanged consumer have compiled;
final delivery validation is recorded by the delivery tool.

New helper theorems contain zero holes:

- `SheafOfModules.PullbackTensorResolving.pullback_resolving_computation`.
- `CategoryTheory.CochainPullback.tensorComparison_commShift`.

Holes added: zero. Remaining split-off holes: zero. Axiom inspection confirms that the main
theorem and both new helper theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the public imports `Sheaf.Paper.RingedTopoiDerivedPullback` and
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`. Their concrete wrappers impose
universe identifications absent from this item's statement. Resolving computation and generic
tensor-comparison descent supply the required argument for the given independently sized data.
Consequently this proof does not use the declared nodes
`lem-weil-pbc-ringed-topoi-derived-pullback` or
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` as proof lemmas.

The old direct proof references to `lem-weil-pbc-site-derived-tensor-descent` and
`lem-weil-pbc-total-tensor-integer-shifts` are unnecessary: their published tensors and shift
structures are exposed by `lem-weil-pbc-kflat-fixed-tensor-triangulated`. These nodes remain
transitive dependencies. Their declarations and the item's statement dependencies are preserved.
No blueprint unit statement or step is bypassed, and no module is withdrawn.

The new proof removes 216 existing project modules from this item’s import closure;
the complete list follows below.

The full `lem-pur-cochain-pullback-tensor-coherence` theorem is no longer used as a proof
lemma: its naturality and action-unit components are supplied directly by the proved
`lem-pur-cochain-comparison-monoidal-equations` API. Its module still supplies published cochain
objects and remains imported; the node remains a statement dependency and approved unit tool.

The complete list of project modules leaving this item's import closure is below. This is an
item-local import calculation, not a claim that these modules are unused by other targets.
All existing declarations remain in their original modules.

- `Sheaf.Algebra.Homology.AcyclicKFlatTensor`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Homology.ChangeOfRingsAcyclicKFlat`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso`
- `Sheaf.Algebra.Homology.KFlatClosure`
- `Sheaf.Algebra.Homology.KFlatResolution`
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`
- `Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTowerLimit`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTowerRepresentation`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleModelRingPresentation`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying`
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction`
- `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`
- `Sheaf.CategoryTheory.ModuleInverseImageAction`
- `Sheaf.CategoryTheory.ModuleInverseImageActionOfPresentations`
- `Sheaf.CategoryTheory.ModuleInverseImageAdjunction`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.CategoryTheory.SheafPullbackForgetComparison`
- `Sheaf.CategoryTheory.SheafPullbackUnitPresentation`
- `Sheaf.CategoryTheory.SiteInverseImageTensor`
- `Sheaf.Paper.DerivedPullbackRepresentativeComputation`
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`
- `Sheaf.Paper.ProfiniteTestObjectFunctor`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct`
- `WeilConjectures.Algebra.Homology.BoundedAboveFlatTensorAcyclic`
- `WeilConjectures.Algebra.Homology.BoundedAboveFlatTensorAcyclicDegree`
- `WeilConjectures.Algebra.Homology.BoundedFlatReplacement`
- `WeilConjectures.Algebra.Homology.ChangeOfRingsTensorAcyclic`
- `WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison`
- `WeilConjectures.Algebra.Homology.CyclePullbackCore`
- `WeilConjectures.Algebra.Homology.CyclePullbackLaws`
- `WeilConjectures.Algebra.Homology.CyclePullbackLifting`
- `WeilConjectures.Algebra.Homology.CyclePullbackResolution`
- `WeilConjectures.Algebra.Homology.CyclePullbackTower`
- `WeilConjectures.Algebra.Homology.CyclePullbackTowerComparison`
- `WeilConjectures.Algebra.Homology.FilteredColimitsTensor`
- `WeilConjectures.Algebra.Homology.FilteredColimitsTensorTotal`
- `WeilConjectures.Algebra.Homology.FlatAugmentationEpicification`
- `WeilConjectures.Algebra.Homology.FlatCoverFunctor`
- `WeilConjectures.Algebra.Homology.FlatTruncationSuccessor`
- `WeilConjectures.Algebra.Homology.FlatTruncationTelescopeComparison`
- `WeilConjectures.Algebra.Homology.FlatTruncationTower`
- `WeilConjectures.Algebra.Homology.KFlat`
- `WeilConjectures.Algebra.Homology.KFlatTensorConeTwoOutOfThree`
- `WeilConjectures.Algebra.Homology.RelativeFlatExtension`
- `WeilConjectures.Algebra.Homology.TelescopeColimit`
- `WeilConjectures.Algebra.Homology.TelescopeShiftMono`
- `WeilConjectures.Algebra.Homology.TruncationTelescope`
- `WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor`
- `WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch`
- `WeilConjectures.CategoryTheory.Adjunction.RingAdjunctPreservesOperations`
- `WeilConjectures.CategoryTheory.Adjunction.RingCoadjunctPreservesOperations`
- `WeilConjectures.CategoryTheory.Adjunction.RingHomEquivCore`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.AcyclicSwallowing`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.CardinalGenerated`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.CardinalGeneratedCover`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Coefficients`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.GeneratingMonoQuasiIsos`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeCardinal`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeEnlargement`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeGeneratingSet`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeSmallObject`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Subcomplex`
- `WeilConjectures.CategoryTheory.ModuleObjects.Abelian`
- `WeilConjectures.CategoryTheory.ModuleObjects.Bimod`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`
- `WeilConjectures.CategoryTheory.ModuleObjects.Preadditive`
- `WeilConjectures.CategoryTheory.Monoidal.Conjugate`
- `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`
- `WeilConjectures.CategoryTheory.Monoidal.Mod.Limits`
- `WeilConjectures.CategoryTheory.RingObjects.Ab`
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`
- `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions`
- `WeilConjectures.CategoryTheory.Sites.MonObj`
- `WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal`
- `WeilConjectures.CategoryTheory.Sites.TransfinitePlus`
- `WeilConjectures.CategoryTheory.Sites.TransfinitePlusSheaf`
- `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives`
- `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.KInjective`
- `WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.FiniteProducts`
- `WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FilteredColimits`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `WeilConjectures.Mathlib.Algebra.Category.Ring.Limits`
- `WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `WeilConjectures.Mathlib.Algebra.Homology.Double`
- `WeilConjectures.Mathlib.Algebra.Homology.ExactSequence`
- `WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors`
- `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`
- `WeilConjectures.Mathlib.Algebra.Homology.SingleHomology`
- `WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic`
- `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.CommSq`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject`
- `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Limits`
- `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`
- `WeilConjectures.Mathlib.CategoryTheory.Comma.CardinalArrow`
- `WeilConjectures.Mathlib.CategoryTheory.Equivalence`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.Flat`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Adjunction`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Preserves`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly`
- `WeilConjectures.Mathlib.CategoryTheory.Generator.Abelian`
- `WeilConjectures.Mathlib.CategoryTheory.Generator.StrongGenerator`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.HasLimits`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.PiProd`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms`
- `WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor`
- `WeilConjectures.Mathlib.CategoryTheory.Localization.Bousfield`
- `WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mon`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation`
- `WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.CommaSites`
- `WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Limits`
- `WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction`
- `WeilConjectures.Mathlib.CategoryTheory.NatIso`
- `WeilConjectures.Mathlib.CategoryTheory.Presentable.Limits`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.CompatiblePlus`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Equivalence`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Grothendieck`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Localization`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Plus`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering`
- `WeilConjectures.Mathlib.CategoryTheory.SmallObject.TransfiniteIteration`
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.FactorThru`
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.HasCardinalLT`
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.Lattice`
- `WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc`
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`
- `WeilConjectures.Mathlib.RingTheory.Etale.Weakly`
- `WeilConjectures.Mathlib.SetTheory.Cardinal.HasCardinalLT`
- `WeilConjectures.Mathlib.Topology.Category.TopCat.Limits.Pullbacks`
- `WeilConjectures.Mathlib.Topology.Connected.TotallyDisconnected`
- `WeilConjectures.Mathlib.Topology.Inseparable`
- `WeilConjectures.Mathlib.Topology.QuasiSeparated`
- `WeilConjectures.Mathlib.Topology.Separation.Hausdorff`
- `WeilConjectures.Mathlib.Topology.Sober`
- `WeilConjectures.Mathlib.Topology.Spectral.Basic`
- `WeilConjectures.Mathlib.Topology.Spectral.Prespectral`
- `WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal`
- `WeilConjectures.Topology.SpectralSpace.ConnectedComponent`
- `WeilConjectures.Topology.SpectralSpace.Profinite`
- `WeilConjectures.Topology.SpectralSpace.Pullback`

## Where the brief, the DAG or earlier work was wrong

The item allows independent site-object, site-morphism, coefficient, and derived-category
universes. The older concrete derived-pullback interfaces identify some of these levels, so they
cannot directly implement this statement. The new resolving-computation theorem retains all its
universes and derives computation from the supplied universal pair, rather than selecting a
replacement pullback.

The prescribed cochain comparison already agrees with the general additive bifunctor comparison.
That identification supplies both shifts, including negative shifts and the second-input Koszul
sign. The unit complex has its sole nonzero term in degree zero; the cochain unit equations impose
no flatness condition on the structural ring map. The argument includes zero coefficient rings and
unbounded complexes.

## New nodes

- `lem-weil-pbc-pullback-resolving-computation`: computation of the given universal derived
  comparison on flat-term K-flat complexes, with independent universes; proved.
- `lem-weil-pbc-cochain-pullback-tensor-shift`: both signed shift compatibilities of the prescribed
  cochain comparison, via the additive bifunctor comparison; proved.

Change record: `coord/changes/C7-pullback-tensor-canonical-shift-unit.md`.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
