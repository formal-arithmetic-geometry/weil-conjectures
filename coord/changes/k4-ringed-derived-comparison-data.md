# CategoryTheory.RingedDerivedComparisons.System

## Reason

Move the existing witness records into `Sheaf.SixFunctors.RingedDerivedComparisonData`
so separate mathematical normalization results can use them without an import cycle.
The original item publicly imports that module and keeps its theorem name and statement.
No target, definition body, record field, binder or universe changes. The source-library
root `WeilConjectures` is untouched. This is an interface-location change, not a
mathematical definition repair or a split to evade a compile limit.

The moved declarations are Site, Site.ring/modules/D/sets/corner, Morphism, Lift,
Lift.insertion/alpha/tensor/unit, Composition, Identity, TwoIso and System, all in
CategoryTheory.RingedDerivedComparisons. Their existing names, field signatures,
bodies and effective visibility stay the same. The new module uses an exposed
public section; the two explicit expose annotations on corner/insertion are thus
redundant and omitted. Docstring blueprint links now name the data node. All original public imports are re-exported via the new module.

## Old

In `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`:

```lean
structure System where
  lift : ∀ {X Y : Site.{u, w}}, (f : Morphism X Y) → Lift f
  composites : ∀ {X Y Z : Site.{u, w}} (f : Morphism X Y) (g : Morphism Y Z),
    ∃ (k : Morphism X Z) (θ : k.inverse ≅ g.inverse ⋙ f.inverse),
      k.ringMap = θ.hom.app ((sheafCompose Z.J
        (CategoryTheory.forget CommRingCat.{u})).obj Z.A) ≫
          f.inverse.map g.ringMap ≫ f.ringMap
  identities : ∀ X : Site.{u, w},
    ∃ (f : Morphism X X) (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))),
      f.ringMap = θ.hom.app ((sheafCompose X.J
        (CategoryTheory.forget CommRingCat.{u})).obj X.A)
  composition : ∀ {X Y Z : Site.{u, w}} (f : Morphism X Y) (g : Morphism Y Z)
    (k : Morphism X Z) (θ : k.inverse ≅ g.inverse ⋙ f.inverse),
    k.ringMap = θ.hom.app ((sheafCompose Z.J
      (CategoryTheory.forget CommRingCat.{u})).obj Z.A) ≫
        f.inverse.map g.ringMap ≫ f.ringMap →
    Nonempty (Composition (lift f) (lift g) (lift k) θ)
  identity : ∀ (X : Site.{u, w}) (f : Morphism X X)
    (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))),
    f.ringMap = θ.hom.app ((sheafCompose X.J
      (CategoryTheory.forget CommRingCat.{u})).obj X.A) → Nonempty (Identity (lift f) θ)
  twoIso : ∀ {X Y : Site.{u, w}} (h k : Morphism X Y) (θ : h.inverse ≅ k.inverse),
    h.ringMap = θ.hom.app ((sheafCompose Y.J
      (CategoryTheory.forget CommRingCat.{u})).obj Y.A) ≫ k.ringMap →
    Nonempty (TwoIso (lift h) (lift k) θ)
```

## New

The identical declaration is in `Sheaf.SixFunctors.RingedDerivedComparisonData`,
publicly imported by the original module:

```lean
structure System where
  lift : ∀ {X Y : Site.{u, w}}, (f : Morphism X Y) → Lift f
  composites : ∀ {X Y Z : Site.{u, w}} (f : Morphism X Y) (g : Morphism Y Z),
    ∃ (k : Morphism X Z) (θ : k.inverse ≅ g.inverse ⋙ f.inverse),
      k.ringMap = θ.hom.app ((sheafCompose Z.J
        (CategoryTheory.forget CommRingCat.{u})).obj Z.A) ≫
          f.inverse.map g.ringMap ≫ f.ringMap
  identities : ∀ X : Site.{u, w},
    ∃ (f : Morphism X X) (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))),
      f.ringMap = θ.hom.app ((sheafCompose X.J
        (CategoryTheory.forget CommRingCat.{u})).obj X.A)
  composition : ∀ {X Y Z : Site.{u, w}} (f : Morphism X Y) (g : Morphism Y Z)
    (k : Morphism X Z) (θ : k.inverse ≅ g.inverse ⋙ f.inverse),
    k.ringMap = θ.hom.app ((sheafCompose Z.J
      (CategoryTheory.forget CommRingCat.{u})).obj Z.A) ≫
        f.inverse.map g.ringMap ≫ f.ringMap →
    Nonempty (Composition (lift f) (lift g) (lift k) θ)
  identity : ∀ (X : Site.{u, w}) (f : Morphism X X)
    (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))),
    f.ringMap = θ.hom.app ((sheafCompose X.J
      (CategoryTheory.forget CommRingCat.{u})).obj X.A) → Nonempty (Identity (lift f) θ)
  twoIso : ∀ {X Y : Site.{u, w}} (h k : Morphism X Y) (θ : h.inverse ≅ k.inverse),
    h.ringMap = θ.hom.app ((sheafCompose Y.J
      (CategoryTheory.forget CommRingCat.{u})).obj Y.A) ≫ k.ringMap →
    Nonempty (TwoIso (lift h) (lift k) θ)
```

All other moved declarations are verbatim, apart from equivalent expose placement
noted above and local elaboration options. There is no added axiom or data choice.
The data node owns their Lean attachments; the original node retains its existence theorem.

## Users

The repair preflight additionally found the six `RingedCoefficient` consumers
listed below: AssociatorShifts, ProjectionData, PullbackCoherence,
PullbackComparison, PullbackShifts and ScalarUnits. Each row records the
exact references reported by server preflight and checks their preservation
by unchanged definitions and public re-export. No consumer code is changed.

The return at head `545ebfab82` additionally identifies
`Sheaf.Paper.OpenRestrictionScalarExchange`, which mentions `Site.D` and
`Lift.unit`. It is listed below even though its source and claim are absent
from this machine's current snapshot. The landing report supplies the two
references; their unchanged definitions and public re-export preserve both.
The fresh local source scan finds 48 current transitive importers, all already
listed; the earlier conservative list is retained to cover server consumers.

At the previous submission, a source-only scan of both library roots with the
packet imports overlaid found 1,086 transitive importers of the item. That scan
superseded the earlier cached 47-module list used for the first submission. The check below conservatively
includes all importers, not just textual matches of the moved declarations, plus
the packet modules. The short names D, unit, ring and tensor occur in unrelated
contexts too; those matches are unaffected. The original declarations and their
public availability are unchanged for every entry, so no mathematical statement
or target definition changes and no adaptation of a held module is needed.

All six record declarations were compared verbatim. The unchanged direct importer
DerivedBaseChangeMap was compiled against the packet. Every other listed effect
follows from the unchanged declarations and their public re-export; no claim is
made that every transitive consumer was individually compiled by this worker.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Algebra.Homology.DerivedTensorTruncationWindow` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.CartierKummerMap` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.CompactProductArrows` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.CompactProductRealizationArrows` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.TraceCupNaturality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleGenericEvaluationCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | C5 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.FrobeniusFactorization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.GenericFiberComponentsSection` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralConstantCompletion` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.KunnethSupported` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.OrdinaryEtaleCupFunctoriality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.ProperSupportCompactMaps` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.SfEtaleExchanges` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.SheafExtCoherent` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.SupportLongExact` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | P7 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | S3 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | U2 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.CategoryTheory.DerivedBaseChangeMap` | unclaimed | Direct importer; compiled unchanged against this packet. |
| `Sheaf.CategoryTheory.ThreeStepAdjunctionComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicHeartPullbackFibres` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicLocalCharacteristicFactor` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicPullbackPresentationTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicPunctualWeights` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicPurityFiniteTensor` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicPurityRootComparisons` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicPuritySourceReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicPurityTwistReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicSmoothBaseChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicSuppliedModelFlatCriterion` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicTorFlatCohomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdicTorFlatCriterion` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AffineLineInvariance` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AffineLineOrdinaryInvariance` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AffineSpaceRationalInduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AmbientCompleteCoefficientCategories` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AmbientCompleteRawSystem` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AmbientIndDerivedSums` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.AmbientIndDerivedTriangulated` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.BoundaryDualizingComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.BoundaryHomVanishing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.BoundaryOrdinaryImages` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.BoundaryQFoundation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.BoundaryQMaps` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.BoundaryQTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.BoundedConstructibleBaseChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.BoundedConstructiblePushforwardRestriction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.BoundedExchangeAmbient` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.BrownExceptionalAdjoint` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.BrownHypothesesGeneration` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CanonicalCoefficientPullbackReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CanonicalRingedRefinementShape` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CanonicalRingedRefinementSquare` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CartesianCoefficientTwists` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CartesianCoefficients` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CartesianCoefficientsFiniteFree` | E2 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ClopenStrictSystemComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ClosedAdjointConstructibleYoneda` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ClosedSupportConstructible` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ClosedSupportedCupVanishing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefTowerCoaugmentation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientDerivedFunctorAPI` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientExchangeFromComparisons` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | Z9 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientFiniteDescentHom` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientFiniteDescentObjects` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientFiniteDescentSections` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientHeart` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientHeartClosure` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientHeartFiltration` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientHeartGeneration` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientHeartLisseExtensionConstructible` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientHeartSheafConeWitness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientHeartTriangulated` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientTowerGeometricComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientTowerSectionCoordinates` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekInterfaces` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoefficientTowerTransitionCompatibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoherentRationalPullbackIdentity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CohomologicalSmoothComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonAdicCompactificationSectionData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonStageCalculus` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonStageCompactSupportExactness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonStageLisse` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonStageLocallyFree` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonStagePullbackIdentity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonStageWeilLinearDual` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactProductProperSupportCompatibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactProductProperSupportLaws` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactProductRealizationCoreLaws` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactProductRealizationLaws` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactProductTwistLaws` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactSupportCoefficientAction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactSupportFiniteAction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactSupportReductionTower` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactSupportReductionTowerConstruction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactSupportRepresentativeIndependence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactSupportUniformTorBound` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactificationLocalizing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactificationRefinementIdentity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompactificationRefinementLocalizing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompatibleFiniteDerivedTrivializations` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompleteCompactSupportProetale` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompleteProetale` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompletedCoefficientPresentationTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompletedCompactSupportExchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompletedExchangeCoherence` | S9 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompletedMapReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompletedPullbackReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompletedReductionSquare` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompletedStalkFrobeniusReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CompletedTensorScalarLinearity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedClosedCostalkDerivedContinuity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedCompactSupportProjection` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedConstructibleExtensionTower` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedConstructibleOneStep` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedConstructibleOpenClosedImages` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedERealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedFiniteCoefficientLocalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedFiniteModelExtensions` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedLocalPieceCostalkModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedLocalPieceHomContinuity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedLocallyClosedExtensionTower` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedLocallyClosedOneStep` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedOpenClosedRecollement` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedOpenExceptionalProjectionFormula` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedPointCoefficients` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedPointDiscreteConstantComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeLeftAdjunct` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedQbarExchangeRightAdjunct` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedQbarPullbackCube` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedStratumModelAssembly` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedStratumModelInductionStep` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonempty` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CondensedTateRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstantToContinuousScalarFlat` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstantWeilStructure` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstructibleCompactness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstructibleCompactnessBounded` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstructibleExtContinuity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstructibleHomComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstructibleHomContinuityDevissage` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstructibleInternalHomContinuity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstructibleProjectionMates` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstructiblePullbackTExact` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ConstructibleTruncations` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperFiniteness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperHeartFiniteness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousAlgClProperLowerTail` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralDenominators` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralGluing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralImage` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralSingle` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralStratum` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousConstructibleIntegralTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousEtaleLocalLattices` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousExchangeIntegralModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousFiniteFreeKernelModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralComparisons` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralComplexTelescope` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralExchangeEquality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralExchangeSquare` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationContinuity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationCounit` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationHomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationLegs` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationMate` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralLocalizationModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralModuleTelescope` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralPullComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralPushComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralRegularTelescope` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousIntegralUnderivedPushComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousLatticeFiniteCoproduct` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousLatticeIntersectionLocalModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousLatticeIntersectionRationalModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousLatticeIntersectionRationalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousLatticeIntersectionSplitData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousLatticeIntersectionSplitModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousLisseCoefficientDescent` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousLissePullbackSystem` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousLisseStratifiedLattices` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousLisseStratumDescent` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousQbarExceptionalPreservation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CurveMiddleExtension` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.CurveWeilMiddleExtension` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DenseOpenPiOneSurjective` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DerivedDirectImageOpenCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DerivedGeometricStalk` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DerivedNakayama` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DerivedNakayamaFirstReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DerivedNakayamaResolution` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DerivedPullbackTensorHom` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DerivedPullbackTensorIso` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DerivedTruncationCoproducts` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DetIndHeartIISums` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DeterminantalWeightCoefficientField` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DiagonalTowerLimit` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DiagonalTowerSystem` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceCoefficients` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceLimit` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DiagonalTowerTraceModels` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DiagonalTowerTracePresentations` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DirectImageChangeRingTranspose` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DirectImagesConstructible` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DlLocallyConstructibleAdicHeart` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.DualizingObjectPurity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ECoefficientSmoothBaseChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.EtaleCoefficientSystemAdjoint` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.EtaleCompactScalarCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.EtaleCompactSupportCoefficientChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.EtaleHomFiniteTorAmplitude` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.EtaleIsoDescent` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.EtaleLocallyClosedShriek` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.EtaleProEtaleCoefficientTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.EtaleProEtaleScalarMate` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.EtaleRhoMonoidalMate` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.EtaleSitePerfectConstructibleHom` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ExceptionalFiniteRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ExceptionalFiniteSupportRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ExceptionalProEtaleRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ExceptionalSiteRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ExtensionZeroPerfectModelTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ExtensionZeroStratifiedPerfect` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ExternalRHomConePairing` | J7 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FdCoefficientComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FdCoefficientComparisonSystem` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FdPullbackComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FieldShriekLowerBound` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FieldStageOrdinaryRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FieldTorAmplitude` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FieldTwistInverse` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FilteredCoefficientTensorBounds` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteClosedShriek` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteCoefficientDescentTwoColimit` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteCoefficientDirectImage` | C4 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteCoefficientHomChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteCoefficientPoint` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteCoefficientReductionFlatModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteCompactSupportConstructibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteCompactSupportScalarComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteCompactSupportScalarTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteConstantModelResolution` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteConstructibleHom` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteCoefficientEncoding` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteCoefficientExchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteCoefficientRestriction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteConstructibleEncoding` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteDerivedCoefficientData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteEncodedPresentation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteExchangeComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteExchangeRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteRealizationFunctor` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDiscreteRestrictionEncoding` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteEtaleAdicCohomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteExtensionReductionConeBound` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteFieldInternalHomFiniteness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteForwardProductSymmetry` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | T5 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteFreeCompactScalar` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteFreeScalarProjection` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteModelStratumFiltration` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FinitePerfectAdicRealization` | B3 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteProjectionActionLaws` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteProperBaseChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteProperLocalizing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FinitePullbackTensorComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteReductionChartCalculus` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteReductionComparisons` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteReductionRootCharts` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteRingSectionDeformation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothAdjunctionData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothCoefficientArrows` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothGammaNormalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothLevelOfOrientation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothPurityMaps` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothQuotientCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothSiteRealizations` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteSmoothTwoLevelReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteSystemPullbackCoherence` | M3 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteTateSiteDescent` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteWindow` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteWindowBounded` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FiniteWindowUnbounded` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FixedStalkIdentificationReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FormalClosedSupport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FormalClosedSupportDerived` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FormalClosedSupportII` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FormalClosedSupportIILimits` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FormalClosedSupportSheaves` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FourierAdicArtinSchreier` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FourierTraceFunctions` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionMap` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FrobeniusCompactSupportExchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FrobeniusGeometricExchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.FrobeniusSquareExchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.GeometricStalkPerfect` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.HomFiniteProjective` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IdentificationFibreAdjunction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IndConstructibleExtensions` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IndConstructibleFilteredColimits` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IndHeartCanonicalPresentation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IndHeartFullFaithfulness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IndHeartIIVanishing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IndHeartKernelsCokernels` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralCanonicalTruncations` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralCoefficientExtComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralCoherenceTower` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralCohomologicalAdicCriterion` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralComparisonRealizationModels` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralConstantModelHeart` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleCompactness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleExt` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleHeart` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleReductionFibres` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleSequentialHom` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralConstructibleSheafHom` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralCriterionReductions` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralCtfTriangulated` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralDerivedCoefficientData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | M2 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralExchangeReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralExtensionByZero` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralFiniteExchangeComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralHeartDualizable` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralHeartLocalDualityDescent` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralHeartLocalModel` | C2 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralHeartRealizationExact` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralHeartResidueDual` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralIndConstructibleHeartClosure` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralIndConstructibleStability` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralIndHeartRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralIndLowerTail` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralModelSurjectiveClosedReflection` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralModels` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralModelsOperations` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralOpenExtensionReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralOpenImageProperFormulas` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralProperCohomologicalBounds` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralProperDirectSums` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralProperProjectionFormula` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralProperReductionBound` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralProperReductionModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralPullbackComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralPullbackReductionCounit` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralPullbackResolutionMatching` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralPullbackSystemComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralRationalQbarCompactSupport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralResidueExchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralResidueExchangeAlgebra` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralStratumExtBound` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralStratumHomFormula` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralSystemPullbackLiftAssociativity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralSystemReductionFullyFaithful` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralTStructure` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralTensorProduct` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralTensorPullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralTensorShriek` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralTowerInverseImageUnit` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralTowerLimitComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralTwistBaseChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralTwistDerivedScalar` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralTwistDerivedScalarCanonical` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralTwistScalarCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntegralWindowCoproductComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.InterchangeProperPasting` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.InternalHomDualConstructibleModels` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.InternalHomDualTorAmplitude` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.InternalHomPullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntrinsicCoefficientTwists` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IntrinsicQbarCategory` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.InverseImagePullbackComparisonDerived` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IsomorphismDerivedPullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.KummerAdditivity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LevelwiseAdicTruncations` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LisseEConstructibleIntegralLattice` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LisseIntegralCompletedRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LisseNormalizedTowerLocalModels` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LocalFrobeniusTrace` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LocalizedTStructure` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LocalizedTensorBraidingNaturality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LocalizingClosureCtfEqualsBc` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LocalizingLowerShriekCompositionModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.LocallyConstantPerfectComplex` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.MateOpenRestriction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.MixedReductionUnit` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.MixedWeightsStability` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ModelCompactComparisonUnit` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ModuleRingedToposDerivedComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.NoetherianEtaleSectionSpecialization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.NonrationalCompositionSeed` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.NonrationalLocalizingLowerShriekComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.NormalProEtaleMonodromy` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.NormalizedCoefficientFamilies` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.NormalizedDerivedIsomorphismSectionReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.NormalizedDerivedIsomorphismTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.NormalizedRationalEvaluationNaturality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.OpenExtensionConstantModelConstructible` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.OpenFiltrationSuccessor` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.OpenImmersionLocalizing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.OpenRestrictionScalarExchange` | unclaimed in current local claims | Uses `CategoryTheory.RingedDerivedComparisons.Site.D` and `CategoryTheory.RingedDerivedComparisons.Lift.unit`; both declarations are unchanged and publicly re-exported, so no source adaptation. |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.OrdinaryCompactWeilCohomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.OrdinaryCompletedIntegralPullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PadicIntegersInvertEll` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcCoefficientTwists` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcCohomologySheaves` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcCommonStageCones` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcConeIndependence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcConstructibleReductionCriterion` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcConstructibleReductionPullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcDescentFunctors` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcDistinguishedDiagramLifting` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcFiniteRawScalarComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcFiniteStageKaroubian` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcIdempotentCompleteTriangulation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcIntrinsicTowerComplete` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcQbarCategory` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcQbarCompletedPullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcQbarIdempotentComplete` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcQbarStandardCohomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcRationalTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcScalarExtension` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcSupportCondition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcUniformCompleteTriangulated` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcUniformLocalModelCohomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcUniformReductionCriterion` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PbcVerdierAxioms` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensor` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensorBasic` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensorFiniteModels` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensorModels` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensorQbar` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensorRational` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PointFibreDerivedTensorScalar` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PointFibreEquivalence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PointIdentityAdmissibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PointRealizationCoefficientComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PointSectionsReconstruction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProEtaleCompositionTowerNormalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProEtalePerfectHomTorAmplitude` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProEtaleProjectionExchangeMaps` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProEtaleSectionModuleFunctors` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProEtaleTateTwists` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProEtaleTateTwistsOfUniverses` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProjectionCoefficientTensorTotal` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProjectionFiniteReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProjectionSectionNormalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperExceptionalRestriction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperHeartBoundLattice` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperHeartBoundReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperHeartBoundTorsion` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperHeartConstructibleCohomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperIndConstructibleBoundedBelow` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperIndConstructibleUnbounded` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperLocalizingAdmissibleCoefficients` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperLocalizingContinuousAlgCl` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperOpenCoefficientMate` | V3 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperUnboundedCoproductComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperUnboundedCoproducts` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperUnboundedWindow` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperUnboundedWindowBounded` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ProperUnboundedWindowIso` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PunctualSpectrumExactFibre` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurAdicScalarExtensionTorBound` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurIntegralTwistLineInverseImage` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientationInjectivity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityAffineLineOrientationUniqueness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityCompositionCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityConventions` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityCoprojection` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityDiagonalOrientationCompatibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityDncFamilyIntrinsic` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityExteriorProductFrame` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityFiniteKummerLevel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityGeneralAdmissibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityGysinStructure` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityRelativeKummer` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PuritySourceTransports` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.PurityTwistCancellation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.QbarCoefficientSmoothBaseChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.QbarCohomologyFiniteLevelComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.QbarCurveOrdinaryImage` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.QbarIdempotentComplete` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.QbarPerverseSubcategories` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.QbarPerverseSupportCondition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.QbarTwistCommonStage` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.QcqsCompactSupportRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.QuotientCornerFrobeniusStructures` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RationalClosedSupportConstructible` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RationalDirectImageRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RationalExceptionalRestriction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RationalHomScalarTranspose` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RationalLocalizingProjectionFormula` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RationalOpenDirectImageConstructible` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RationalRealizationTensorComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RationalRestrictionGlue` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RationalScalarTransposeCompatibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RationalTensorSymmetry` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RationalVerdierEvaluationAdjoints` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RealSheafSections` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ResidueLissePerfectLift` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ResidueLisseProjectiveModels` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RestrictionLocal` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RingedCoefficientAssociatorShifts` | unclaimed in current local claims | Uses `CategoryTheory.RingedDerivedComparisons.Site.D`; unchanged definitions and public re-export preserve these references; no source adaptation. |
| `Sheaf.Paper.RingedCoefficientProjectionCocycle` | R4 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RingedCoefficientProjectionData` | unclaimed in current local claims | Uses `CategoryTheory.RingedDerivedComparisons.Site.modules`, `CategoryTheory.RingedDerivedComparisons.Site.D`, `CategoryTheory.RingedDerivedComparisons.Lift.insertion`; unchanged definitions and public re-export preserve these references; no source adaptation. |
| `Sheaf.Paper.RingedCoefficientPullbackCoherence` | unclaimed in current local claims | Uses `CategoryTheory.RingedDerivedComparisons.Site.D`, `CategoryTheory.RingedDerivedComparisons.Lift.unit`; unchanged definitions and public re-export preserve these references; no source adaptation. |
| `Sheaf.Paper.RingedCoefficientPullbackComparison` | unclaimed in current local claims | Uses `CategoryTheory.RingedDerivedComparisons.Site.D`; unchanged definitions and public re-export preserve these references; no source adaptation. |
| `Sheaf.Paper.RingedCoefficientPullbackShifts` | unclaimed in current local claims | Uses `CategoryTheory.RingedDerivedComparisons.Site.modules`, `CategoryTheory.RingedDerivedComparisons.Site.D`; unchanged definitions and public re-export preserve these references; no source adaptation. |
| `Sheaf.Paper.RingedCoefficientScalarUnits` | unclaimed in current local claims | Uses `CategoryTheory.RingedDerivedComparisons.Site.D`, `CategoryTheory.RingedDerivedComparisons.Lift.unit`; unchanged definitions and public re-export preserve these references; no source adaptation. |
| `Sheaf.Paper.RingedRefinementClopen` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RingedRefinementCoefficientSquare` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RingedRefinementConstruction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RingedRefinementCore` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RingedRefinementData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.RingedRefinementFinite` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SbcCompletedOperations` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ScalarExchangeConstituents` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ScalarExtensionExactIntrinsic` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ScalarExtensionTensorUnit` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SectionDerivedRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SectionDerivedTensorData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SectionModuleOperationsData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SemilinearDerivedSections` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SemilinearOperationsExistence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SemilinearSystemsExistence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfAlgebraicallyClosedCoefficients` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfBidualityClass` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfCbcExtensionZeroCompletion` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfCommonStageDirectImage` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfCommonStageWeilCohomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfConstructibleHeart` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfExchanges` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfImmersionCompletedPullbackComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfIntegralConstructibleLinear` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfIntegralConstructibleTriangulated` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfIntegralPullbackLinearAdjunction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfIntegralStandardTruncations` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfLocalizationAllStages` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfRationalBoundedConeTorsion` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfRationalDirectImageAdjunction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfRationalizationKaroubi` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfScalarExtensionComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SfWeilSheafComplex` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SignedTwistReductionComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SiteComparisonEdgeSection` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SitePerfectCoefficientDual` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SitePerfectComplex` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SitePerfectDualizableHom` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SitePerfectRationalBidual` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SixFunctorDatum` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SixFunctorDualNotation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SixFunctorOperationDatum` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SmoothPullbackSupportDimension` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SmoothPurityMap` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SmoothPurityNormalizedEquivalence` | Z7 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SmoothPurityReductionTowerNormalized` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SmoothPurityTowerBound` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SmoothPurityTowerClasses` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SmoothPurityTowerP1Adjunction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SmoothPurityTowerReconstruction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SmoothTrace` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SpecifiedHomScalarEvaluation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.StratifiedLattice` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.StratifiedLatticeRank` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SupportedAffineLineHomotopy` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SupportedClassGeometry` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SupportedClassSiteComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SupportedCupFunctoriality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SupportedExteriorClassArrows` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SupportedExteriorClasses` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SupportedExteriorShift` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SupportedHomPullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SupportedTwistDegreeZeroProduct` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SupportedTwistMultiplication` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SupportedTwistPullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SystemNormalizedTensorClosure` | H3 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SystemOperationExchangeRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.SystemTensorMateArrows` | H8 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TAdmissibleCoefficientModels` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TAdmissibleDualizableTruncations` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TateTwistLisseLine` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TateTwistLocallyFree` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TensorAdjunctionExchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TopologicalStratifiedLisseLattices` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TowerClassChern` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TowerClassCoefficients` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TowerClassDiagonal` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TowerClassFinite` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TowerClassFiniteDiagonal` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TowerClassProjective` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TowerClassPullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TowerClassReduction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TowerClassSystems` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TowerClassTwisting` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TraceBaseChangeFirst` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TraceBaseChangeSecond` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TraceCohomologicalCorrespondence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TraceFormulaCurveIntegralLattice` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TraceFormulaDualizingComplex` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TraceFormulaStrictWeilComplex` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TraceFormulaTopologicalInvariance` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TrfDevissageGeneration` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TwConventions` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.TwistPreservesFiniteness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.UnboundedBaseChangeExtension` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.UniformConstructibleExt` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.UniformConstructibleExtIntegral` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.UniformConstructibleExtRational` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.UniformConstructibleExtTorsion` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.VectorBundlePurity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.WContractibleCondensedScalarEvaluation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.WeilCompactSupportCohomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.WeilComplexQbarIdempotentComplete` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.WeilComplexTraceFunction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.WeilIndSheafCategory` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | U1 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.ReductionDirectImageComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.RestrictionTransitionTranspose` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SecSmoothPurity.WeilTwistRationalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.BoundaryDualityInput` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.BrownHypothesesAmbient` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.BrownHypothesesSmall` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.ClosedImmersionTensorProjection` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdier` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.CompactCoefficientComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.ConstructibleTensorCompletion` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.CtfStabilityDirectImages` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FieldTensor` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FiniteCoverCTFLocality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FiniteDualizing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FiniteExceptional` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntTensorProjection` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralBrownAdjoint` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralComplementFiniteness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralDualizing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineChart` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalAffineFactorization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralExceptionalRestriction` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionOccurrences` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralExtHomContinuity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralLocalizingCompactSupport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionBoundedDescent` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionChartCover` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionClosed` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionGlue` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralRestrictionLine` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralSystemExpressionDomain` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralSystemOperations` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralTensorInverseImage` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.IntegralVerdier` | V2 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.OpenFactorCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.OpenFactorPullModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.OpenFactorTensorModel` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.OpenImmersionTensorProjection` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.ProEtale.DerivedCompletion` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.ProperImageLocalizingProper` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.RationalOperations` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.RationalRetractEvaluation` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.RationalVerdier` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.ResolvingDerivedAdjunction` | K4 (this packet) | Packet module; compiled against the relocated unchanged record API. |
| `Sheaf.SixFunctors.RingedDerivedAdjointLift` | K4 (this packet) | Packet module; compiled against the relocated unchanged record API. |
| `Sheaf.SixFunctors.RingedDerivedComparisonData` | K4 (this packet) | Packet module; compiled against the relocated unchanged record API. |
| `Sheaf.SixFunctors.RingedDerivedCompositionComparison` | K4 (this packet) | Packet module; compiled against the relocated unchanged record API. |
| `Sheaf.SixFunctors.RingedDerivedIdentityComparison` | K4 (this packet) | Packet module; compiled against the relocated unchanged record API. |
| `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons` | K4 (this packet) | Packet module; compiled against the relocated unchanged record API. |
| `Sheaf.SixFunctors.RingedDerivedTensorDiagrams` | K4 (this packet) | Packet module; compiled against the relocated unchanged record API. |
| `Sheaf.SixFunctors.RingedDerivedTensorLift` | K4 (this packet) | Packet module; compiled against the relocated unchanged record API. |
| `Sheaf.SixFunctors.RingedDerivedTwoIsoComparison` | K4 (this packet) | Packet module; compiled against the relocated unchanged record API. |
| `Sheaf.SixFunctors.ScalarSixPullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.SchemeFrobenius` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisPullbackNaturality` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | S4 | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.SuppliedTensorAdjunctionNormalization` | K4 (this packet) | Packet module; compiled against the relocated unchanged record API. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Targets.AffineSpaceRationalLine` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Targets.PoincareTateBoundedConstructible` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Targets.PoincareUncurry` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Targets.SmoothPurityQbar` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Targets.VectorBundlePurity` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.Topology.ProfiniteCondensedRing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.TraceFormula.BigSmallEtaleLocalizationDerivedPushforward` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.TraceFormula.PointTransportComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.WeilSheaf.AdicFiniteCoefficientBound` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.WeilSheaf.AffineCurveRangePositive` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.WeilSheaf.FiniteBoundaryPositive` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.Defs` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.TensorHom` | unclaimed | Unchanged record API through public re-export; no source adaptation. |
| `WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar` | unclaimed | Unchanged record API through public re-export; no source adaptation. |

## Status

landed 20261020T233155-L-902653 2026-10-20 (merge of deliver/K4/Sheaf.SixFunctors.RingedDerivedMonoidalComparisons)
