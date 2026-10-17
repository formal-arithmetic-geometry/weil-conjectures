# AlgebraicGeometry.ProEtale.CondensedRing.exists_condensedQbar_scalar_basis_sections

## Reason

The full proof adds private categorical helpers, auxiliary universes, namespace blocks,
`open MonObj` commands, and a local elaboration option. The conservative interface checker
classifies these command changes as an interface change and requires this record.
Every existing public declaration has exactly its old signature. There is no changed public
definition, instance or target statement, and no consumer needs an adaptation. The new point
basis result is a proof import with its own node.

## Old

The existing public theorem signature, verbatim:

```lean
theorem exists_condensedQbar_scalar_basis_sections :
    ∃ (I : Type (u + 1))
      (b : ∀ Z : Scheme.{u}, I →
        (𝟙_ (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) ⟶
          condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)),
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (i : I), b X i =
        Functor.LaxMonoidal.ε (f)^*[Ab.{u + 1}] ≫
          (f)^*[Ab.{u + 1}].map (b Y i) ≫
            condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f) ∧
      (∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z))) ∧
      (∀ (Z : Scheme.{u})
        (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E) Z))
        [HasCoproduct (fun _ : I ↦ N)],
        IsIso (Sigma.desc (f := fun _ : I ↦ N) fun i ↦
          (Mod.extendRestrictAdjunction (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).unit.app N ≫
          (Mod.comap (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).map
            (Mod.qbar_scalarEndo (b Z i) ((Mod.extendScalars (coefficientMap
              (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).obj N))))
```

Original command setup:

```lean
universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
```

## New

The same public theorem signature, verbatim:

```lean
theorem exists_condensedQbar_scalar_basis_sections :
    ∃ (I : Type (u + 1))
      (b : ∀ Z : Scheme.{u}, I →
        (𝟙_ (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) ⟶
          condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z)),
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (i : I), b X i =
        Functor.LaxMonoidal.ε (f)^*[Ab.{u + 1}] ≫
          (f)^*[Ab.{u + 1}].map (b Y i) ≫
            condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) f) ∧
      (∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z))) ∧
      (∀ (Z : Scheme.{u})
        (N : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E) Z))
        [HasCoproduct (fun _ : I ↦ N)],
        IsIso (Sigma.desc (f := fun _ : I ↦ N) fun i ↦
          (Mod.extendRestrictAdjunction (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).unit.app N ≫
          (Mod.comap (coefficientMap
            (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).map
            (Mod.qbar_scalarEndo (b Z i) ((Mod.extendScalars (coefficientMap
              (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) Z)).obj N))))
```

The proof now has private helper sections in `CategoryTheory.Mod` and
`AlgebraicGeometry.ProEtale`, with `universe u v w`, `open MonObj`, and generic categorical
variables scoped to those sections. All extra declarations in the existing module are
private and proved. `scheme_basis_from_point` keeps the coefficient objects abstract to
avoid expensive reduction of concrete coefficient-ring constructions in coherence.
The unchanged theorem is instantiated from the fully proved
`Profinite.exists_padicAlgCl_point_basis`. No target definition changes meaning and no
statement review is reopened by a definition change.

## Users

The read-only `tools/downstream.py ... --uses exists_condensedQbar_scalar_basis_sections`
check found 106 downstream modules and two textual uses (the defining module and
`Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisUnit`). The complete listed module set is
recorded below. Holder information is the current claim state at the time of writing;
none of these consumers is adapted by this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexColimit | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexCompatibility | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDerivedTransport | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexModel | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexUnderivedCompatibility | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasis | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisSections | B4 | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisUnit | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedCoefficientFamilyHomStage | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedCoefficientHomStage | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | C1 | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedFinitePresentationMatrices | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedFpHomStage | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedLocalCoefficientAdjoints | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedQbarPullbackCube | E1 | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenPiece | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | C4 | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| TargetsCheck | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| WeilConjectures | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | No statement, definition or consumer edit; same theorem signature. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | No statement, definition or consumer edit; same theorem signature. |

## Status

landed 20261017T021559-L-693603 2026-10-17 (merge of deliver/B4/Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisSections)
