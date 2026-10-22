# AlgebraicGeometry.Scheme.tateTwist_locallyFree

## Reason

The proof needs the pro-etale sheafification and derived-category constructions at
explicit universes. Five private aliases select the existing standard constructions
at those universes, with high-priority **local** instance registrations.
Four aliases are proved private theorems; the data-valued derived-category
alias is an instance-reducible private definition. The ordinary
`HasDerivedCategory.standard` registration is also local. No instance is exported,
and no imported instance is removed. This avoids repeated inference through large
completed-tensor definitions without changing any public data or declaration type.

The preflight conservatively classifies new attribute commands as an interface
change and requires this record. The item is held by V7. No other module is edited,
and no declaration of the adopted source library is changed. No target statement or
definition used by a target changes meaning, so no statement review is reopened.

## Old

The original public-section options, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
```

There were no `tateAbSheafify`, `tateAbBijective`, `tateWeakSheafify`, `tateSiteSmall`
or `tateDerived` declarations or associated instance registrations. All original
public definitions and their bodies remain verbatim.

The original theorem signature, verbatim:

```lean
theorem tateTwist_locallyFree
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    (ι : E →ₐ[Padic ℓ] Ω) :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 X))
      (ζ : ∀ (n : ℕ) (i : I), (purTwistRootsModule X ℓ n).val.obj (op (U i)))
      (e : ∀ (n : ℕ) (i : I),
        (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ n))).over (U i) ≅
          (purTwistRootsModule X ℓ n).over (U i)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _ ∧
      (∀ (n : ℕ) (i : I),
        (proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op (U i))
            (ζ (n + 1) i) = ζ n i) ∧
      (∀ (n : ℕ) (i : I) (V : (Over (U i))ᵒᵖ)
        (a : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V),
        (e n i).hom.val.app V a =
          a • (purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n i)) ∧
      (∀ (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ),
        (∀ a : A, (ℓ ^ (r + 1)) • a = 0) →
        ∃ a : ZMod (ℓ ^ (r + 1)) →+* A,
          (∀ (n : ℕ) (hrn : r ≤ n),
            ∃ k : tateFiniteLine X ℓ A n
                (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                  (ZMod (ℓ ^ (r + 1))))) ⟶ tateFiniteLine X ℓ A r a,
              IsIso k ∧
              ∀ (V : X.ProEt) (b : (tateFiniteCoefficient X A).obj.obj (op V))
                (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)),
                k.val.app (op V)
                  (tateFiniteTensor X ℓ A n
                    (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                      (ZMod (ℓ ^ (r + 1))))) V b x) =
                  tateFiniteTensor X ℓ A r a V b
                    ((proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
                      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
                      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) x)) ∧
          (∃ hL : (tateFiniteLine X ℓ A r a).IsFiniteLocallyFreeOfRank 1,
            TateSignedLine X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) U ∧
            ∀ n : ℕ, TateInverseTwists
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL n)
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL
                (-(n : ℤ))))) ∧
      TateSignedLine X (completedIntegralCommRingSheafUnrestricted ℓ E X)
        (purTwistIntegralModule X ℓ E) U ∧
      ∀ (D : FiniteFieldDatum.{d}) (hD : ℓ ≠ D.p),
        TateRationalSignedLine D ℓ hD E X U ∧
        TateQbarSignedLine D ℓ hD X Ω U ∧
        ∀ n : ℕ, TateInverseTwists (tateIntegralTwist D ℓ hD E X n)
          (tateIntegralTwist D ℓ hD E X (-(n : ℤ))) ∧
        TateInverseTwists (tateRationalTwist D ℓ hD E X n)
          (tateRationalTwist D ℓ hD E X (-(n : ℤ))) ∧
        TateInverseTwists (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω n)
          (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω (-(n : ℤ)))
```

## New

Keep the original options and add the following setup after the original public
definitions, before the proved private helpers and the unchanged theorem statement:

```lean
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] HasDerivedCategory.standard

private theorem tateAbSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X
attribute [local instance 20000] tateAbSheafify
private theorem tateAbBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X
attribute [local instance 20000] tateAbBijective

private theorem tateWeakSheafify (X : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  (tateAbSheafify X).isRightAdjoint
attribute [local instance 20000] tateWeakSheafify

private theorem tateSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance 20000] tateSiteSmall

@[instance_reducible] private def tateDerived (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} (purTwistRing X R)) :=
  HasDerivedCategory.standard _
attribute [local instance 20000] tateDerived
```

These aliases have complete constructions. They contain no `sorry`. In particular,
there is no global `instance` command and no negative instance-attribute command.
The theorem's proof docstring and DAG proof describe the implemented argument.

The theorem signature remains verbatim:

```lean
theorem tateTwist_locallyFree
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (Ω : Type v) [Field Ω] [Algebra (Padic ℓ) Ω] [IsAlgClosure (Padic ℓ) Ω]
    (ι : E →ₐ[Padic ℓ] Ω) :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 X))
      (ζ : ∀ (n : ℕ) (i : I), (purTwistRootsModule X ℓ n).val.obj (op (U i)))
      (e : ∀ (n : ℕ) (i : I),
        (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ n))).over (U i) ≅
          (purTwistRootsModule X ℓ n).over (U i)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _ ∧
      (∀ (n : ℕ) (i : I),
        (proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op (U i))
            (ζ (n + 1) i) = ζ n i) ∧
      (∀ (n : ℕ) (i : I) (V : (Over (U i))ᵒᵖ)
        (a : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V),
        (e n i).hom.val.app V a =
          a • (purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n i)) ∧
      (∀ (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ),
        (∀ a : A, (ℓ ^ (r + 1)) • a = 0) →
        ∃ a : ZMod (ℓ ^ (r + 1)) →+* A,
          (∀ (n : ℕ) (hrn : r ≤ n),
            ∃ k : tateFiniteLine X ℓ A n
                (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                  (ZMod (ℓ ^ (r + 1))))) ⟶ tateFiniteLine X ℓ A r a,
              IsIso k ∧
              ∀ (V : X.ProEt) (b : (tateFiniteCoefficient X A).obj.obj (op V))
                (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)),
                k.val.app (op V)
                  (tateFiniteTensor X ℓ A n
                    (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                      (ZMod (ℓ ^ (r + 1))))) V b x) =
                  tateFiniteTensor X ℓ A r a V b
                    ((proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
                      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
                      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) x)) ∧
          (∃ hL : (tateFiniteLine X ℓ A r a).IsFiniteLocallyFreeOfRank 1,
            TateSignedLine X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) U ∧
            ∀ n : ℕ, TateInverseTwists
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL n)
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL
                (-(n : ℤ))))) ∧
      TateSignedLine X (completedIntegralCommRingSheafUnrestricted ℓ E X)
        (purTwistIntegralModule X ℓ E) U ∧
      ∀ (D : FiniteFieldDatum.{d}) (hD : ℓ ≠ D.p),
        TateRationalSignedLine D ℓ hD E X U ∧
        TateQbarSignedLine D ℓ hD X Ω U ∧
        ∀ n : ℕ, TateInverseTwists (tateIntegralTwist D ℓ hD E X n)
          (tateIntegralTwist D ℓ hD E X (-(n : ℤ))) ∧
        TateInverseTwists (tateRationalTwist D ℓ hD E X n)
          (tateRationalTwist D ℓ hD E X (-(n : ℤ))) ∧
        TateInverseTwists (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω n)
          (intrinsicQbarComplexTwistFunctor D ℓ hD X Ω (-(n : ℤ)))
```

## Users

`tools/downstream.py Sheaf.Paper.TateTwistLocallyFree --uses tateTwist_locallyFree
 tateAbSheafify tateAbBijective tateWeakSheafify tateSiteSmall tateDerived` finds
only the item and `Sheaf.Paper.FieldTwistInverse` as textual theorem users and no
users of the private aliases. The following table additionally lists every
transitive importer conservatively, with the current claim holder. All receive
the same public statements, definitions and instance environment. No consumer is
adapted. Compilation of the item and the normal delivery checks validate the
packet; the maintainer's global build remains the independent whole-library check.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | claimed | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | unclaimed | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Unchanged; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Unchanged; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Unchanged; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | claimed | Unchanged; no adaptation. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTower | claimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CondensedBoundedHomContinuity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DerivedOpenSquareRestriction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Uses tateTwist_locallyFree with its unchanged type; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | claimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | claimed | Unchanged; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralAmbientCoefficientPresentation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralAmbientDirectImageEncoding | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralAmbientTowerComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientCoefficients | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionMap | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | claimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChangeDefinitions | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistSchemeCompatibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LatticeSubquotientFiltration | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LisseLatticePotentialKummerTameness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LocalizedDirectImageComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityConventions | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.QcqsRationalIntegralLocalizingGenerators | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.QlbarDirectImageComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | claimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RealWeights | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | claimed | Unchanged; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RootBoundaryComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ScalarModelImmersionExtension | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | claimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.StratifiedConstantModelProductBound | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.StratifiedLatticeRank | claimed | Unchanged; no adaptation. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TameRootTowerExtension | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | claimed | V7 item; proof-local aliases only; existing public data and signatures unchanged. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | claimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WfTateTwist | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | claimed | Unchanged; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Unchanged; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | claimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | claimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | claimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | Unchanged; no adaptation. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Unchanged; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Unchanged; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Unchanged; no adaptation. |
| TargetsCheck | unclaimed | Unchanged; no adaptation. |
| WeilConjectures | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Unchanged; no adaptation. |

## Status

landed 20261022T002501-L-1933458 2026-10-22 (merge of deliver/V7/Sheaf.Paper.TateTwistLocallyFree)
