# Diagonal dualizing definitions extracted for an acyclic proof decomposition

## Reason

The gluing, coordinate-normalization and rigidity statements must refer to the
ordinary dualizing object and normalization predicate before the main existence
and uniqueness theorem is proved. Extracting the existing data into a preceding
module removes that import cycle. This is a mathematical dependency extraction;
no timeout prompted it. Every existing declaration retains its exact name,
signature, body and visibility. The item publicly reexports the data module.
No target statement or definition meaning changes. No adapted consumer is needed.

## Old

The following definitions and proved theorem were declared directly in
lean/Sheaf/Paper/PurityDiagonalDualizingObject.lean:

```lean
/-- The ordinary-etale presentation of the relative dualizing object, applied to
A_Y in degree zero. Source: blueprint exceptional inverse image, finite stage
(blueprint: thm-pur-diagonal-dualizing-object). -/
def diagonalOrdinaryDualizing (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :=
  (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f).obj
    (Etale.ordinaryFiniteUnit P.Coefficient Y)

/-- The finite transported exceptional inverse image of the coefficient unit.
This uses the recorded sfFiniteExceptionalAt at its specified compactification;
it is an object of D(X_proet,A), not of D(X_et,A).
Source: blueprint def-weil-exceptional-inverse-image, displayed finite definition
(blueprint: thm-pur-diagonal-dualizing-object). -/
def diagonalDualizing (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriek f P.Coefficient
  letI : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient)
      (HasCompactification.compactification f)).IsLeftAdjoint :=
    inferInstanceAs (Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} P.Coefficient) f).IsLeftAdjoint
  (ProEtale.sfFiniteExceptionalAt P.Coefficient
    (HasCompactification.compactification f)).obj
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit P.Coefficient Y))

/-- The actual degree-zero coefficient object is bounded below.
Source: blueprint coefficient unit, A_Y[0]
(blueprint: thm-pur-diagonal-dualizing-object).
Proof: the single complex has cohomology A in degree zero and zero in every other
degree, so zero is a lower bound in the standard t-structure. -/
theorem diagonalUnitPlus (P : PurityFiniteSetting.{u}) (Y : Scheme.{u}) :
    _root_.DerivedCategory.TStructure.t.plus (Etale.ordinaryFiniteUnit P.Coefficient Y) := by
  exact ⟨0, inferInstance⟩

/-- The canonical identification with nu_X* f^times A_Y, by the inverse of the
comparison adjunction unit at the bounded-below coefficient object.
Source: blueprint exceptional inverse image and finite comparison
(blueprint: thm-pur-diagonal-dualizing-object). -/
def diagonalDualizingComparison (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    P.diagonalDualizing f ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
          (P.diagonalOrdinaryDualizing f) :=
  letI := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} P.Coefficient) Y
      (Etale.ordinaryFiniteUnit P.Coefficient Y) (P.diagonalUnitPlus Y)
  (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
      ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) f).mapIso
        (asIso ((ProEtale.derivedComparisonAdjunction
          (ModuleCat.{u + 1} P.Coefficient) Y).unit.app
            (Etale.ordinaryFiniteUnit P.Coefficient Y))).symm)

/-- Canonical source-etale locality, with the specified sum-extension counit.
The normalized compact-support comparison N fixes the mate completely.
Source: blueprint etale locality of the exceptional adjoint
(blueprint: thm-pur-diagonal-dualizing-object). -/
def diagonalEtaleLocality (P : PurityFiniteSetting.{u})
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    {U X Y : Scheme.{u}} (j : U ⟶ X) (f : X ⟶ Y)
    [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian Y]
    [HasCompactification f] [HasCompactification (j ≫ f)] :
    (Etale.ordinaryFinitePullback P.Coefficient j).obj (P.diagonalOrdinaryDualizing f) ≅
      P.diagonalOrdinaryDualizing (j ≫ f) :=
  (Etale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} P.Coefficient) j).app _ ≪≫
    (Etale.tensorMateEtalePrecompLocalityIso P.Coefficient N j f).app
      (Etale.ordinaryFiniteUnit P.Coefficient Y)

/-- The actual affine-space trace, transposed under the ordinary exceptional
adjunction. It is a map from the ordered shifted-root-line coefficient object;
no arbitrary affine-space orientation is an input.
Source: blueprint affine-space trace and its normalized counit
(blueprint: thm-pur-diagonal-dualizing-object). -/
def diagonalAffineMate (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (P.diagonalExponent : Γ(Y, ⊤))) (d : ℕ) :
    P.diagonalTwistEtale (affineTraceTower Y d) d ⟶
      P.diagonalOrdinaryDualizing (affineTraceProjection Y d) :=
  letI := affineTraceNoetherian Y d
  let hN := pow_pos P.coefficients.prime.out.pos P.level
  ((Etale.affineLinearCoefficientDescent P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t Y hY d) ≪≫
    Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t (affineTraceProjection Y d) hY d).inv ≫
    (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient)
      (affineTraceProjection Y d)).homEquiv _ _
        ((Etale.affineLinearCompactComparison P.diagonalExponent hN P.Coefficient
          P.diagonalExponent_annihilates Y hY d).inv ≫
          Etale.affineTraceCounit P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t D Y hY d)

/-- Changing only the displayed composite uses the equality-induced isomorphism.
The compactification witnesses are propositions, hence proof irrelevant.
Source: blueprint canonical functor comparisons
(blueprint: thm-pur-diagonal-dualizing-object). -/
def diagonalDualizingCongr (P : PurityFiniteSetting.{u})
    {U Y : Scheme.{u}} {f g : U ⟶ Y} [HasCompactification f] [HasCompactification g]
    (w : f = g) : P.diagonalOrdinaryDualizing f ≅ P.diagonalOrdinaryDualizing g :=
  eqToIso (by cases w; rfl)

/-- The coordinate normalization of the inverse orientation. It compares the two
source-etale locality maps on every chart U -> X, U -> A^d_Y over Y. The affine
map is the actual Kummer-normalized counit mate. All normalized coefficient and
compact-support presentations are universally quantified, so none is an extra
hypothesis or an independent choice of orientation.
Source: blueprint canonical diagonal/DNC/vector-bundle orientation
(blueprint: thm-pur-diagonal-dualizing-object). -/
def DiagonalOrientationNormalization (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y) [HasCompactification f]
    [IsNoetherian X] [IsNoetherian Y]
    (aY : Y ⟶ Spec (.of P.field.k))
    (e : P.diagonalOrdinaryDualizing f ≅ P.diagonalTwistEtale X d) : Prop :=
  letI := affineTraceNoetherian Y d
  ∀ (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (U : Scheme.{u}) [IsNoetherian U]
    (j : U ⟶ X) [Etale j] [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    (v : U ⟶ affineTraceTower Y d) [Etale v] [IsSeparated v]
    [LocallyOfFiniteType v] [QuasiCompact v]
    (w : v ≫ affineTraceProjection Y d = j ≫ f)
    [HasCompactification (j ≫ f)] [HasCompactification (v ≫ affineTraceProjection Y d)],
    (Etale.ordinaryFinitePullback P.Coefficient j).map e.inv ≫
        (P.diagonalEtaleLocality N j f).hom =
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t j (P.diagonalExponent_isUnit (f ≫ aY)) d).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t v
          (affineTraceInvertible P.diagonalExponent Y (P.diagonalExponent_isUnit aY) d)
            d).inv ≫
      (Etale.ordinaryFinitePullback P.Coefficient v).map
        (P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) d) ≫
      (P.diagonalEtaleLocality N v (affineTraceProjection Y d)).hom ≫
      (P.diagonalDualizingCongr w).hom

/-- The full-domain canonical pro-etale comparison. No absolute separatedness is
assumed. Noetherianity, quasi-compactness and compactifiability are consequences
of the finite-type field domain. The comparison equation explicitly identifies
the pro-etale arrow with its normalized ordinary presentation.
Source: blueprint smooth purity and its finite exceptional-inverse-image domain
(blueprint: thm-pur-diagonal-dualizing-object). -/
def DiagonalDualizingConclusion (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] : Prop :=
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI := isNoetherian_of_locallyOfFiniteType (f ≫ aY)
  letI : HasCompactification f := inferInstance
  ∃! θ : P.diagonalDualizing f ≅ P.diagonalTwist X d,
    ∃ e : P.diagonalOrdinaryDualizing f ≅ P.diagonalTwistEtale X d,
      P.DiagonalOrientationNormalization d f aY e ∧
      θ = P.diagonalDualizingComparison f ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso e
```

## New

The entire block above, verbatim in its signatures and bodies, is in
lean/Sheaf/Paper/PurityDiagonalDualizingData.lean. Its public imports are precisely
the original public imports. The item publicly imports this module and keeps
existsUnique_diagonalDualizingObject and diagonalDualizingObject. The theorem's
statement and the final definition's body are unchanged. The main proof imports
three new proof-only modules for ordinary gluing, coordinate normalization, and
rigidity. These statements do not choose data. The data node records the moved
block; the original node retains the original mathematical statement and records
the new proof route. Downstream modules receive the same exported declarations
through the public import, including all previous public prerequisites.

## Users

All transitive source importers from the source scan are listed below. No source
library module is changed or removed. All listed effects are preservation of the
existing interface; current holder entries are the local read-only claim snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactors | S9 | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.ChartExceptionalMateCoherence | W3 | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceSiteComparison | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | A4 | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorPresentationReduction | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteTensorSignedReduction | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.GeneralChartComparisons | G6 | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | N2 | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | B4 | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionTower | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartComparison | Z9 | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.Paper.VectorModelChartDescent | W7 | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed (no local claim record) | Unchanged names, signatures, bodies and public prerequisites through reexport; no adaptation. |

## Status

landed 20261025T101229-L-3673535 2026-10-25 (merge of deliver/K3/Sheaf.Paper.PurityDiagonalDualizingObject)
