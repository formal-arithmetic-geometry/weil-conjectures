# sfFiniteOperations realization declarations

## Reason

The normalized restricted-adjunction obligation and the exceptional-bound obligation
both use the pre-existing realization formulas. They must be stated in separate
modules imported by ExceptionalFiniteOperations. Relocate the helper declarations
verbatim into ExceptionalFiniteRestrictionAdjunction and publicly re-export that
module from their original module to avoid an import cycle. Their names, universe
parameters, signatures, visibility, instance attributes and bodies are identical.
The existence theorem retains its original signature. This is an interface
relocation, not a changed mathematical definition. No source-library file changes.

## Old

The following declarations were in Sheaf.Paper.ExceptionalFiniteOperations:

```lean
/-- Finiteness at a positive level, with the existing coefficient quotient unchanged.
Source: Zheng, finite coefficient convention
(blueprint: lem-sf-exceptional-finite-operations). -/
instance sfFiniteOperationsCoefficientFinite (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+) :
    Finite (Padic.coefficientExtensionRing l E.carrier n) :=
  Padic.finite_coefficientExtensionRing l E.carrier n n.pos

/-- The ordinary etale adjoint at this specified compactification is supplied by the
published Brown theorem, rather than by an assumed ambient pro-etale adjunction.
Source: Zheng, Proposition 2.23 (blueprint: lem-sf-exceptional-finite-operations). -/
instance sfFiniteOperationsEtaleLeftAdjoint (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E.carrier n))) c).IsLeftAdjoint :=
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification _ c

/-- The full inclusion followed by the canonical coefficient realization inverse.
This changes coefficient coordinates only, retaining all ambient derived morphisms.
Source: blueprint full finite-Tor categories and site comparison
(blueprint: lem-sf-exceptional-finite-operations). -/
abbrev sfFiniteOperationsRealization (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+) (T : Scheme.{u}) :=
  (finiteTorConstructible l E.carrier n n.pos T).ι ⋙
    (sfIntrinsicDerivedEquivalence T (Padic.coefficientExtensionRing l E.carrier n)).inverse

/-- The realization uses the termwise exact coefficient equivalence and the full
triangulated inclusion, hence their canonical derived shifts.
Source: blueprint ambient integer-shift realization
(blueprint: lem-sf-exceptional-finite-operations). -/
instance sfFiniteOperationsRealizationShift (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+) (T : Scheme.{u}) :
    (sfFiniteOperationsRealization l E n T).CommShift ℤ :=
  inferInstanceAs (((finiteTorConstructible l E.carrier n n.pos T).ι ⋙
    (sfIntrinsicModuleEquivalence T
      (Padic.coefficientExtensionRing l E.carrier n)).inverse.mapDerivedCategory).CommShift ℤ)

/-- The specified etale right adjoint has the adjoint shift structure.
Source: Zheng, Proposition 2.23
(blueprint: lem-sf-exceptional-finite-operations). -/
instance sfFiniteOperationsEtaleRightShift (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E.carrier n))) c).rightAdjoint.CommShift ℤ :=
  (Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E.carrier n))) c)).rightAdjointCommShift ℤ

/-- The fixed-coordinate exceptional composite uses the derived comparison shifts.
Source: blueprint exceptional inverse image
(blueprint: lem-sf-exceptional-finite-operations). -/
instance sfFiniteOperationsExceptionalShift (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (ProEtale.sfFiniteExceptionalAt
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n)) c).CommShift ℤ :=
  inferInstanceAs (((ProEtale.comparisonLowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E.carrier n))) Y).rightDerivedFunctor ⋙
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E.carrier n))) c).rightAdjoint ⋙
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E.carrier n))) X).mapDerivedCategory).CommShift ℤ)

/-- The intrinsic conjugate of the specified-c exceptional functor. Parentheses retain
its canonical coefficient cancellation, with no freely chosen realization.
Source: blueprint exceptional inverse image
(blueprint: lem-sf-exceptional-finite-operations). -/
def sfFiniteOperationsIntrinsicRight (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ((sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E.carrier n)).inverse ⋙
    ProEtale.sfFiniteExceptionalAt
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n)) c) ⋙
    (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E.carrier n)).functor

/-- The inverse-coordinate compact-support comparison, obtained only by cancellation
of the unit and counit in the published normalized comparison.
Source: blueprint proper/open comparison
(blueprint: lem-sf-exceptional-finite-operations). -/
def sfFiniteOperationsSupportComparison (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E.carrier n) ⋙
        (sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E.carrier n)).inverse ≅
      (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E.carrier n)).inverse ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E.carrier n))) c :=
  (Iso.inverseCompIso
    ((Iso.compInverseIso (ProEtale.sfIntrinsicCompactSupportComparison
      (Padic.coefficientExtensionRing l E.carrier n) c)).symm ≪≫
        Functor.associator _ _ _)).symm

/-- The realization of a literal restriction of the recorded intrinsic support functor.
The equality fixes objects and morphisms; its proof cannot absorb an automorphism.
Source: blueprint full finite-Tor restriction
(blueprint: lem-sf-exceptional-finite-operations). -/
def sfFiniteOperationsLeftRealization (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (F : finiteTorConstructibleCategory l E.carrier n n.pos X ⥤
      finiteTorConstructibleCategory l E.carrier n n.pos Y)
    (eF : F ⋙ (finiteTorConstructible l E.carrier n n.pos Y).ι =
      (finiteTorConstructible l E.carrier n n.pos X).ι ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E.carrier n)) :
    F ⋙ sfFiniteOperationsRealization l E n Y ≅
      sfFiniteOperationsRealization l E n X ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E.carrier n))) c :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso eF) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfFiniteOperationsSupportComparison l E n c) ≪≫
    (Functor.associator _ _ _).symm

/-- The exceptional realization cancels only the coefficient-equivalence unit.
Its equality hypothesis fixes the restriction on both objects and morphisms.
Source: blueprint full finite-Tor restriction
(blueprint: lem-sf-exceptional-finite-operations). -/
def sfFiniteOperationsRightRealization (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (G : finiteTorConstructibleCategory l E.carrier n n.pos Y ⥤
      finiteTorConstructibleCategory l E.carrier n n.pos X)
    (eG : G ⋙ (finiteTorConstructible l E.carrier n n.pos X).ι =
      (finiteTorConstructible l E.carrier n n.pos Y).ι ⋙
        sfFiniteOperationsIntrinsicRight l E n c) :
    G ⋙ sfFiniteOperationsRealization l E n X ≅
      sfFiniteOperationsRealization l E n Y ⋙ ProEtale.sfFiniteExceptionalAt
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n)) c :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso eG) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Iso.compInverseIso (Iso.refl _)) ≪≫
    (Functor.associator _ _ _).symm

/-- The actual normalized Hom chain, specialized to the quasi-compact field-scheme
case without requiring separated structure maps. Its factors are the proper/open
comparison, the comparison adjunction, the specified ordinary etale adjunction,
comparison full faithfulness, and the retained etale-origin isomorphism.
Source: Zheng, Proposition 2.23, and blueprint class adjunction, clause (2)
(blueprint: lem-sf-exceptional-finite-operations). -/
def sfFiniteOperationsHomEquiv (l : ℕ) [Fact l.Prime]
    (E : ConstructibleExceptionalCoefficients.FieldStage.{u} l) (n : ℕ+)
    (k : Type u) [Field k] {X Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [QuasiCompact sY]
    {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f)
    (M : DerivedCategory.Plus (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n)))))
    (W : FixedEtaleOriginWitness X
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n)) M)
    (L : DerivedCategory.Plus (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n))))) :
    ((ProEtale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E.carrier n))) c).obj M.obj ⟶ L.obj) ≃
      (M.obj ⟶ (ProEtale.sfFiniteExceptionalAt
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E.carrier n)) c).obj L.obj) :=
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  ProEtale.specifiedExceptionalHomEquiv _ c M W L
```

## New

The identical declarations, including docstrings and bodies above, now live in
Sheaf.Paper.ExceptionalFiniteRestrictionAdjunction. The old module adds:

```lean
public import Sheaf.Paper.ExceptionalFiniteRestrictionAdjunction
```

The new module has a separate theorem for the normalized restricted adjunction;
no moved definition uses that theorem. All data in the moved definitions remains
explicitly constructed, and no data is chosen from the new existence obligations.
The parent DAG attachment now lists only its existence theorem; the moved helper
attachments belong to def-sf-finite-operation-realizations. No target statement or
meaning changes, so this relocation does not reopen a target statement review.

## Users

`tools/downstream.py Sheaf.Paper.ExceptionalFiniteOperations` lists these modules.
No existing consumer needs editing. Textual uses of the moved IntrinsicRight helper
occur in the item and Sheaf.SixFunctors.FiniteExceptional; HomEquiv occurs in the item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExceptionalFiniteOperations | Y8 | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | R2 | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | V6 | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.FiniteTorStability | J2 | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.NormalizedSupportEtalePresentation | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | U9 | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientUnitFiniteTor | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientUnitNormalization | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedSystemPullbackPreservation | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramData | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemDuality | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | S2 | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | Q9 | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemDualityCompatibility | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Same names, signatures, instance attributes and bodies through the public re-export; no adaptation. |

## Status

landed 20261025T164918-L-1127780 2026-10-25 (merge of deliver/Y8/Sheaf.Paper.ExceptionalFiniteOperations)
