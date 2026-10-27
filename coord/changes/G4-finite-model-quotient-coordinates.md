# AlgebraicGeometry.ProEtale.FiniteModelQuotient coordinate definitions

## Reason

Extract the existing coordinate definitions into `Sheaf.Paper.FiniteModelSheafQuotientData`
so that independent chart and descent lemmas can use them without importing their parent theorem.
This is an interface factoring; every existing definition name, signature, universe and body
is byte-for-byte preserved. The main theorem signature is preserved. No target meaning changes.
The new definition node records the moved declarations. The item publicly imports the data module.
There are two direct consumers: QcqsIntegralFiniteModelCompleteness uses the theorem unchanged,
and SupportedImageKoszulComparisonNonpositive imports the module without naming these coordinates.
All transitive consumers from tools/downstream.py are listed below; none requires an edit.

## Old

In `Sheaf.Paper.FiniteModelSheafQuotientConstructible`:

```lean
/-- The recorded integral scalar ring. Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
abbrev A := Padic.coefficientExtensionIntegers l E

/-- The recorded positive-level scalar quotient. Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
abbrev R (n : ℕ) := Padic.coefficientExtensionRing l E (n + 1)

/-- The normalized encoding with exactly the recorded quotient topology.
Source: blueprint finite-coefficient coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
abbrev Encoding (n : ℕ) (T : Scheme.{u}) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  FiniteDiscreteOrdinary.Encoding (R l E n) T

/-- The recorded scalar-extension model, with the induced norm topology on A.
Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def model (T : Scheme.{u}) (P : ModuleCat.{u + 1} (A l E)) :
    AdicCompletion.Modules l E T :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  (FiniteConstantModel.modelFunctor (A l E) T).obj P

/-- Derived reduction of a sheaf in degree zero along the actual quotient homomorphism.
Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def reduction (T : Scheme.{u}) (M : AdicCompletion.Modules l E T) (n : ℕ) :
    AdicCompletion.FiniteDerived l E T n :=
  (AdicCompletion.derivedReduction l E T n).obj ((DerivedCategory.singleFunctor _ 0).obj M)

/-- Reduce every entry of the given scalar matrix by the actual quotient homomorphism.
The lift only puts the scalar coordinates in the site's coefficient universe.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def matrix (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    Matrix (Fin b) (Fin a) (ULift.{u + 1} (R l E n)) :=
  fun i j ↦ ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
    (v i j))

/-- The specified reduced scalar linear map, including ranks zero.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def differential (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    ModuleCat.of (ULift.{u + 1} (R l E n)) (Fin a → ULift.{u + 1} (R l E n)) ⟶
      ModuleCat.of (ULift.{u + 1} (R l E n)) (Fin b → ULift.{u + 1} (R l E n)) :=
  ModuleCat.ofHom (matrix l E n a b v).mulVecLin

/-- The literal complex of free quotient modules in degrees -1 and 0.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def scalarComplex (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n))) ℤ :=
  HomologicalComplex.double (differential l E n a b v)
    (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)

/-- Constant realization of that literal two-term scalar complex in ordinary coordinates.
Source: blueprint finite-coefficient coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def ordinaryComplex (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))) :=
  DerivedCategory.Q.obj
    (((constantSheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (scalarComplex l E n a b v))

/-- The original integral scalar matrix in the lifted coordinates of the finite free modules.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def integralDifferential (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    ModuleCat.of (A l E) (Fin a → ULift.{u + 1} (A l E)) ⟶
      ModuleCat.of (A l E) (Fin b → ULift.{u + 1} (A l E)) :=
  ModuleCat.ofHom
    (((LinearEquiv.piCongrRight fun _ : Fin b ↦
        (ULift.moduleEquiv : ULift.{u + 1} (A l E) ≃ₗ[A l E] A l E)).symm.toLinearMap).comp
      (v.mulVecLin.comp
        (LinearEquiv.piCongrRight fun _ : Fin a ↦
          (ULift.moduleEquiv : ULift.{u + 1} (A l E) ≃ₗ[A l E] A l E)).toLinearMap))

/-- Internal coordinates for the literal two-term quotient complex, transported by
exactly the normalized finite coefficient equivalence (not an arbitrary equivalence).
Source: blueprint specified scalar resolution and ordinary coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def internalComplex (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) (e : Encoding l E n T) :
    AdicCompletion.FiniteDerived l E T n :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  e.fixedDerived.inverse.obj (ordinaryComplex l E T n a b v)

/-- The chart calculation for every specified scalar resolution on every member of
any chosen stratification and pro-etale covers. The two cohomology identifications
retain the quotient coefficient action. Source: blueprint Local models and Locality
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def LocalCalculation (V : Scheme.{u}) (M : AdicCompletion.Modules l E V) (n : ℕ)
    (enc : ∀ T : Scheme.{u}, Encoding l E n T) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ∀ (S : Scheme.Stratification V)
    (C : ∀ i : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain i))
    (i : Fin S.n) (j : (C i).I₀) (P : ModuleCat.{u + 1} (A l E))
    (_hP : Module.FinitePresentation (A l E) P)
    (_eP : (CondensedRing.upperStar (DerivedNakayama.integerRing l E)
      ((C i).f j ≫ S.immersion i)).obj M ≅ model l E ((C i).X j) P)
    (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E))
    (w : ModuleCat.of (A l E) (Fin b → ULift.{u + 1} (A l E)) ⟶ P)
    (_hinj : Function.Injective (integralDifferential l E a b v).hom)
    (_hexact : Function.Exact (integralDifferential l E a b v).hom w.hom)
    (_hsurj : Function.Surjective w.hom),
    Nonempty
      (((CondensedRing.moduleObjectDerivedPullback (DerivedNakayama.quotientRing l E (n + 1))
          ((C i).f j ≫ S.immersion i)).obj (reduction l E V M n)) ≅
        internalComplex l E ((C i).X j) n a b v (enc ((C i).X j))) ∧
    Nonempty
      ((DerivedCategory.homologyFunctor _ (-1)).obj
        ((enc ((C i).X j)).fixedDerived.functor.obj
          ((CondensedRing.moduleObjectDerivedPullback
            (DerivedNakayama.quotientRing l E (n + 1))
            ((C i).f j ≫ S.immersion i)).obj (reduction l E V M n))) ≅
        (constantSheaf (Scheme.ProEt.topology ((C i).X j))
          (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
            (kernel (differential l E n a b v))) ∧
    Nonempty
      ((DerivedCategory.homologyFunctor _ 0).obj
        ((enc ((C i).X j)).fixedDerived.functor.obj
          ((CondensedRing.moduleObjectDerivedPullback
            (DerivedNakayama.quotientRing l E (n + 1))
            ((C i).f j ≫ S.immersion i)).obj (reduction l E V M n))) ≅
        (constantSheaf (Scheme.ProEt.topology ((C i).X j))
          (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
            (cokernel (differential l E n a b v))) ∧
    Finite ↥(kernel (differential l E n a b v)) ∧
    Finite ↥(cokernel (differential l E n a b v)) ∧
    Module.FinitePresentation (ULift.{u + 1} (R l E n))
      ↥(kernel (differential l E n a b v)) ∧
    Module.FinitePresentation (ULift.{u + 1} (R l E n))
      ↥(cokernel (differential l E n a b v))

/-- Ordinary boundedness and intrinsic constructibility in the recorded finite-ring
encoding. The explicit finiteness witness installs only the finiteness just asserted
by the main theorem. Source: blueprint finite constructible cohomology clause
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def OrdinaryConclusion (V : Scheme.{u}) (M : AdicCompletion.Modules l E V) (n : ℕ)
    (hf : Finite (R l E n)) (e : Encoding l E n V) : Prop :=
  letI := hf
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  DerivedCategory.TStructure.t.bounded (e.fixedDerived.functor.obj (reduction l E V M n)) ∧
    ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf V
      (ULift.{u + 1} (R l E n))
      ((DerivedCategory.homologyFunctor _ q).obj
        (e.fixedDerived.functor.obj (reduction l E V M n)))

```

## New

The following identical declarations now live in `Sheaf.Paper.FiniteModelSheafQuotientData`;
the item begins with `public import Sheaf.Paper.FiniteModelSheafQuotientData`.

```lean
/-- The recorded integral scalar ring. Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
abbrev A := Padic.coefficientExtensionIntegers l E

/-- The recorded positive-level scalar quotient. Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
abbrev R (n : ℕ) := Padic.coefficientExtensionRing l E (n + 1)

/-- The normalized encoding with exactly the recorded quotient topology.
Source: blueprint finite-coefficient coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
abbrev Encoding (n : ℕ) (T : Scheme.{u}) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  FiniteDiscreteOrdinary.Encoding (R l E n) T

/-- The recorded scalar-extension model, with the induced norm topology on A.
Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def model (T : Scheme.{u}) (P : ModuleCat.{u + 1} (A l E)) :
    AdicCompletion.Modules l E T :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  (FiniteConstantModel.modelFunctor (A l E) T).obj P

/-- Derived reduction of a sheaf in degree zero along the actual quotient homomorphism.
Source: blueprint Local models
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def reduction (T : Scheme.{u}) (M : AdicCompletion.Modules l E T) (n : ℕ) :
    AdicCompletion.FiniteDerived l E T n :=
  (AdicCompletion.derivedReduction l E T n).obj ((DerivedCategory.singleFunctor _ 0).obj M)

/-- Reduce every entry of the given scalar matrix by the actual quotient homomorphism.
The lift only puts the scalar coordinates in the site's coefficient universe.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def matrix (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    Matrix (Fin b) (Fin a) (ULift.{u + 1} (R l E n)) :=
  fun i j ↦ ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
    (v i j))

/-- The specified reduced scalar linear map, including ranks zero.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def differential (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    ModuleCat.of (ULift.{u + 1} (R l E n)) (Fin a → ULift.{u + 1} (R l E n)) ⟶
      ModuleCat.of (ULift.{u + 1} (R l E n)) (Fin b → ULift.{u + 1} (R l E n)) :=
  ModuleCat.ofHom (matrix l E n a b v).mulVecLin

/-- The literal complex of free quotient modules in degrees -1 and 0.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def scalarComplex (n a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    CochainComplex (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n))) ℤ :=
  HomologicalComplex.double (differential l E n a b v)
    (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)

/-- Constant realization of that literal two-term scalar complex in ordinary coordinates.
Source: blueprint finite-coefficient coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def ordinaryComplex (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))) :=
  DerivedCategory.Q.obj
    (((constantSheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (scalarComplex l E n a b v))

/-- The original integral scalar matrix in the lifted coordinates of the finite free modules.
Source: blueprint specified scalar resolution
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def integralDifferential (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E)) :
    ModuleCat.of (A l E) (Fin a → ULift.{u + 1} (A l E)) ⟶
      ModuleCat.of (A l E) (Fin b → ULift.{u + 1} (A l E)) :=
  ModuleCat.ofHom
    (((LinearEquiv.piCongrRight fun _ : Fin b ↦
        (ULift.moduleEquiv : ULift.{u + 1} (A l E) ≃ₗ[A l E] A l E)).symm.toLinearMap).comp
      (v.mulVecLin.comp
        (LinearEquiv.piCongrRight fun _ : Fin a ↦
          (ULift.moduleEquiv : ULift.{u + 1} (A l E) ≃ₗ[A l E] A l E)).toLinearMap))

/-- Internal coordinates for the literal two-term quotient complex, transported by
exactly the normalized finite coefficient equivalence (not an arbitrary equivalence).
Source: blueprint specified scalar resolution and ordinary coordinates
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def internalComplex (T : Scheme.{u}) (n a b : ℕ)
    (v : Matrix (Fin b) (Fin a) (A l E)) (e : Encoding l E n T) :
    AdicCompletion.FiniteDerived l E T n :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  e.fixedDerived.inverse.obj (ordinaryComplex l E T n a b v)

/-- The chart calculation for every specified scalar resolution on every member of
any chosen stratification and pro-etale covers. The two cohomology identifications
retain the quotient coefficient action. Source: blueprint Local models and Locality
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def LocalCalculation (V : Scheme.{u}) (M : AdicCompletion.Modules l E V) (n : ℕ)
    (enc : ∀ T : Scheme.{u}, Encoding l E n T) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ∀ (S : Scheme.Stratification V)
    (C : ∀ i : Fin S.n, Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain i))
    (i : Fin S.n) (j : (C i).I₀) (P : ModuleCat.{u + 1} (A l E))
    (_hP : Module.FinitePresentation (A l E) P)
    (_eP : (CondensedRing.upperStar (DerivedNakayama.integerRing l E)
      ((C i).f j ≫ S.immersion i)).obj M ≅ model l E ((C i).X j) P)
    (a b : ℕ) (v : Matrix (Fin b) (Fin a) (A l E))
    (w : ModuleCat.of (A l E) (Fin b → ULift.{u + 1} (A l E)) ⟶ P)
    (_hinj : Function.Injective (integralDifferential l E a b v).hom)
    (_hexact : Function.Exact (integralDifferential l E a b v).hom w.hom)
    (_hsurj : Function.Surjective w.hom),
    Nonempty
      (((CondensedRing.moduleObjectDerivedPullback (DerivedNakayama.quotientRing l E (n + 1))
          ((C i).f j ≫ S.immersion i)).obj (reduction l E V M n)) ≅
        internalComplex l E ((C i).X j) n a b v (enc ((C i).X j))) ∧
    Nonempty
      ((DerivedCategory.homologyFunctor _ (-1)).obj
        ((enc ((C i).X j)).fixedDerived.functor.obj
          ((CondensedRing.moduleObjectDerivedPullback
            (DerivedNakayama.quotientRing l E (n + 1))
            ((C i).f j ≫ S.immersion i)).obj (reduction l E V M n))) ≅
        (constantSheaf (Scheme.ProEt.topology ((C i).X j))
          (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
            (kernel (differential l E n a b v))) ∧
    Nonempty
      ((DerivedCategory.homologyFunctor _ 0).obj
        ((enc ((C i).X j)).fixedDerived.functor.obj
          ((CondensedRing.moduleObjectDerivedPullback
            (DerivedNakayama.quotientRing l E (n + 1))
            ((C i).f j ≫ S.immersion i)).obj (reduction l E V M n))) ≅
        (constantSheaf (Scheme.ProEt.topology ((C i).X j))
          (ModuleCat.{u + 1} (ULift.{u + 1} (R l E n)))).obj
            (cokernel (differential l E n a b v))) ∧
    Finite ↥(kernel (differential l E n a b v)) ∧
    Finite ↥(cokernel (differential l E n a b v)) ∧
    Module.FinitePresentation (ULift.{u + 1} (R l E n))
      ↥(kernel (differential l E n a b v)) ∧
    Module.FinitePresentation (ULift.{u + 1} (R l E n))
      ↥(cokernel (differential l E n a b v))

/-- Ordinary boundedness and intrinsic constructibility in the recorded finite-ring
encoding. The explicit finiteness witness installs only the finiteness just asserted
by the main theorem. Source: blueprint finite constructible cohomology clause
(blueprint: lem-sfb-finite-model-sheaf-quotient-constructible). -/
def OrdinaryConclusion (V : Scheme.{u}) (M : AdicCompletion.Modules l E V) (n : ℕ)
    (hf : Finite (R l E n)) (e : Encoding l E n V) : Prop :=
  letI := hf
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  DerivedCategory.TStructure.t.bounded (e.fixedDerived.functor.obj (reduction l E V M n)) ∧
    ∀ q : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf V
      (ULift.{u + 1} (R l E n))
      ((DerivedCategory.homologyFunctor _ q).obj
        (e.fixedDerived.functor.obj (reduction l E V M n)))

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose Sheaf.AlgebraicGeometry.ProperHeartBoundRational Sheaf.DeligneLaumon.QbarCurveDuality Sheaf.DeligneLaumon.Reduction.AffineCurveUpper Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel Sheaf.Paper.AdicCommonStageHomTranspose Sheaf.Paper.AdicNormalizedPurityLift Sheaf.Paper.AdicOperationDomainsSourceComparison Sheaf.Paper.AdicProperLocalizingAdjunctionComparison Sheaf.Paper.AdicUnitTraceConstruction Sheaf.Paper.AdicUnitTraceReductionData Sheaf.Paper.AdicUnitTraceScalarData Sheaf.Paper.AdicUnitTraceTensorCoordinates Sheaf.Paper.AdicUnitTraceTransposeReductions Sheaf.Paper.AdmissibleVerdierExchange Sheaf.Paper.AffineCompactificationComparisonNormalization Sheaf.Paper.AffineCounitScalar Sheaf.Paper.AffineLineCanonicalScalarCounit Sheaf.Paper.AffineSpaceRationalInduction Sheaf.Paper.ArithmeticRoots Sheaf.Paper.BrownExceptionalAdjoint Sheaf.Paper.BrownTowerBoundedTransport Sheaf.Paper.BrownTowerFiniteEvaluation Sheaf.Paper.BrownTowerFiniteSiteComparison Sheaf.Paper.BrownTowerGeometricTransport Sheaf.Paper.BrownTowerRealization Sheaf.Paper.BrownTowerSite Sheaf.Paper.CartesianSectionAdjointMates Sheaf.Paper.CartesianSectionData Sheaf.Paper.ChartCounitScalarTransport Sheaf.Paper.ChartDiagonalSourceMate Sheaf.Paper.ChartGeometricCounitEvaluation Sheaf.Paper.ClosedAdjointConstructibleYoneda Sheaf.Paper.CoefSupportOpenTensorModel Sheaf.Paper.CoefSupportPointSectionsData Sheaf.Paper.CoefficientGammaRepresentatives Sheaf.Paper.CoefficientMapGeometricSquares Sheaf.Paper.CoefficientTowerGeometricComposition Sheaf.Paper.CoefficientTowerSectionCoordinates Sheaf.Paper.CoefficientTowerShriekCalculus Sheaf.Paper.CoefficientTowerShriekInterfaces Sheaf.Paper.CoefficientTowerTransitionCompatibility Sheaf.Paper.CohomologicalSmoothEtaleLocality Sheaf.Paper.CommonStageConstituentNonexceptional Sheaf.Paper.CommonStageFourierWeightUpper Sheaf.Paper.CompactificationCoherenceCocycle Sheaf.Paper.CompactificationLocalizing Sheaf.Paper.CompactificationProjectionInverse Sheaf.Paper.CompactificationRefinementIdentity Sheaf.Paper.CompactificationRefinementLocalizing Sheaf.Paper.CompletedStalkFrobeniusReduction Sheaf.Paper.ConcreteIntegralProjectionCone Sheaf.Paper.ConcreteProjectionFieldDescent Sheaf.Paper.CondensedExceptionalReconstruction Sheaf.Paper.CondensedHomChainRealization Sheaf.Paper.ContinuousAlgClProperFiniteness Sheaf.Paper.ContinuousAlgClProperHeartFiniteness Sheaf.Paper.ContinuousAlgClProperLowerTail Sheaf.Paper.ContinuousAlgClProperScalarComparison Sheaf.Paper.ContinuousQbarExceptionalPreservation Sheaf.Paper.CurveIntermediateExtension Sheaf.Paper.CurveMiddleExtensionUpper Sheaf.Paper.DerivedTruncationCoproducts Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation Sheaf.Paper.EtaleAffineProjectionCoefficientMate Sheaf.Paper.EtaleCtfChartDomain Sheaf.Paper.EtaleOpenCounitFlatModels Sheaf.Paper.EtaleProEtaleAdjunctionTransfer Sheaf.Paper.EtaleProEtaleCoefficientCompatibility Sheaf.Paper.EtaleSumCounitScalar Sheaf.Paper.ExceptionalInverseImageExistence Sheaf.Paper.ExceptionalRealizationNormalization Sheaf.Paper.ExceptionalReconstructionComparison Sheaf.Paper.ExceptionalReconstructionContext Sheaf.Paper.ExceptionalReconstructionPresentations Sheaf.Paper.ExceptionalRefinementMates Sheaf.Paper.FiniteAdjointCompositorTransposes Sheaf.Paper.FiniteAdjointMateCompatibility Sheaf.Paper.FiniteCoefficientAdjointComparisons Sheaf.Paper.FiniteCompactSupportDomains Sheaf.Paper.FiniteDiagonalOrientationReduction Sheaf.Paper.FiniteDiagonalReductionComparisons Sheaf.Paper.FiniteDncNormalizationReduction Sheaf.Paper.FiniteFreeCoefficientExtension Sheaf.Paper.FiniteFreeCoefficientExtensionData Sheaf.Paper.FiniteFreeCompactComposition Sheaf.Paper.FiniteFreeCompactScalar Sheaf.Paper.FiniteFreeCompactSupportComposition Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality Sheaf.Paper.FiniteFreeProjectionExchange Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions Sheaf.Paper.FiniteFreeScalarProjection Sheaf.Paper.FiniteLocalizingExceptionalPreservation Sheaf.Paper.FiniteLocalizingSmoothLocalFormula Sheaf.Paper.FiniteProperLocalizing Sheaf.Paper.FiniteTorStability Sheaf.Paper.FiniteUniversalSmoothTrace Sheaf.Paper.FixedStalkIdentificationReduction Sheaf.Paper.GeneralHomComparisonCocycles Sheaf.Paper.GeometricComparisonData Sheaf.Paper.GeometricGeneratorProjectionDevissage Sheaf.Paper.GeometricOperations Sheaf.Paper.GlobalVerdierDuality Sheaf.Paper.HomChainPairingNaturality Sheaf.Paper.IntegralDirectImageTower Sheaf.Paper.IntegralLocalizingProperBaseChange Sheaf.Paper.IntegralOpenImageProperFormulas Sheaf.Paper.IntegralProperBaseChange Sheaf.Paper.IntegralProperCohomologicalBounds Sheaf.Paper.IntegralProperConstructibleHeartBound Sheaf.Paper.IntegralProperDirectSums Sheaf.Paper.IntegralProperProjectionFormula Sheaf.Paper.InterchangeProperPasting Sheaf.Paper.InverseContravariantBidual Sheaf.Paper.LevelwiseNormalizedAdjointDescent Sheaf.Paper.LocalizingExceptionalAdjoint Sheaf.Paper.LocalizingLowerShriekComposition Sheaf.Paper.LocalizingLowerShriekCompositionModel Sheaf.Paper.MateOpenCompactSupportExchange Sheaf.Paper.MateOpenProperRestrictionIso Sheaf.Paper.MateOpenProperSupport Sheaf.Paper.MateOpenRestriction Sheaf.Paper.MateOpenRestrictionMaps Sheaf.Paper.ModelCompactComparisonUnit Sheaf.Paper.NonrationalCompositionSeed Sheaf.Paper.NonrationalLocalizingLowerShriekComposition Sheaf.Paper.NormAlgClInternalHomBaseChange Sheaf.Paper.NormalizedIntegralPurityTrace Sheaf.Paper.NormalizedStageCoefficientCalculus Sheaf.Paper.OpenExceptionalScalarLocality Sheaf.Paper.OpenImmersionLocalizing Sheaf.Paper.OpenProEtaleCounitScalar Sheaf.Paper.OrderedCompactificationScalarSquare Sheaf.Paper.OrderedTateScalarNormalization Sheaf.Paper.P1CounitScalar Sheaf.Paper.P1SplittingScalar Sheaf.Paper.PodCtfAdjunctions Sheaf.Paper.PodCtfPairingMaps Sheaf.Paper.PodHomChainCounitFormula Sheaf.Paper.PodHomChainCtfDomains Sheaf.Paper.PodHomChainUncurriedTransport Sheaf.Paper.ProEtaleProperOpenInterchange Sheaf.Paper.ProjectionFiniteReduction Sheaf.Paper.ProjectionFormulaCoherence Sheaf.Paper.ProperAlgClComparisonDomains Sheaf.Paper.ProperExceptionalRestriction Sheaf.Paper.ProperHeartBound Sheaf.Paper.ProperHeartBoundLattice Sheaf.Paper.ProperIndConstructibleBoundedBelow Sheaf.Paper.ProperIndConstructibleUnbounded Sheaf.Paper.ProperLocalizingAdmissibleCoefficients Sheaf.Paper.ProperLocalizingContinuousAlgCl Sheaf.Paper.ProperOpenBoundaryZero Sheaf.Paper.ProperProductCounitTranspose Sheaf.Paper.ProperUnboundedCoproductComparison Sheaf.Paper.ProperUnboundedCoproducts Sheaf.Paper.ProperUnboundedWindow Sheaf.Paper.ProperUnboundedWindowIso Sheaf.Paper.PurIntegralRepresentingPair Sheaf.Paper.PurIntegralSupportComparison Sheaf.Paper.QbarPerverseSubcategories Sheaf.Paper.QbarPerverseSupportCondition Sheaf.Paper.QcqsIntegralFiniteModelCompleteness Sheaf.Paper.RamifiedReductionComparisonSquare Sheaf.Paper.RamifiedScalarSystemTranspose Sheaf.Paper.RationalAffineAdjunctionCalculus Sheaf.Paper.RationalAffineTensorCalculus Sheaf.Paper.RationalExceptionalRestriction Sheaf.Paper.RationalHomScalarTranspose Sheaf.Paper.RationalP1AmbientComposites Sheaf.Paper.RationalP1KernelContractions Sheaf.Paper.RationalP1Triangle Sheaf.Paper.RationalP1UnitCounit Sheaf.Paper.RationalRestrictionGlue Sheaf.Paper.RationalScalarComparisonIdentification Sheaf.Paper.RationalScalarTransposeCompatibility Sheaf.Paper.RationalTensorSymmetry Sheaf.Paper.RationalVerdierEvaluationAdjoints Sheaf.Paper.RawChartScalarCounitPasting Sheaf.Paper.ReconstructedPairRefinementCoherence Sheaf.Paper.ReductionSiteCoefficientPasting Sheaf.Paper.RelativeKunneth Sheaf.Paper.RelativeProductInputDomains Sheaf.Paper.RestrictionLocal Sheaf.Paper.ScalarExchangeConstituents Sheaf.Paper.SfBidualityClass Sheaf.Paper.SfPackageCoefficientDomains Sheaf.Paper.SfPackageExceptionalCoherenceRealization Sheaf.Paper.SfPackageFieldOperationRealization Sheaf.Paper.ShriekNormalizedTransitionComparison Sheaf.Paper.SitePerfectRationalBidual Sheaf.Paper.SmoothPullbackSupportDimension Sheaf.Paper.SmoothPurityCoordinateCategories Sheaf.Paper.SmoothPurityCoordinateRightComparisons Sheaf.Paper.SmoothPurityCoordinateTensorComparisons Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability Sheaf.Paper.SmoothPurityTowerGamma Sheaf.Paper.SmoothPurityTowerGluing Sheaf.Paper.SmoothPurityTowerReductionTranspose Sheaf.Paper.SupportedImageKoszulComparisonNonpositive Sheaf.Paper.SupportedLatticeNormProjection Sheaf.Paper.SystemProjectionFormulaCoherence Sheaf.Paper.SystemScalarProjectionIdentification Sheaf.Paper.TamePairProperGenerators Sheaf.Paper.TateTwistSupportCondition Sheaf.Paper.TateTwistedProjection Sheaf.Paper.TensorHomCoefficientTransposes Sheaf.Paper.TowerCompactSupportProjectionFormula Sheaf.Paper.TowerProjectionDomainEvaluation Sheaf.Paper.TraceCorrespondences Sheaf.Paper.TraceFormulaDualizingComplex Sheaf.Paper.TraceFormulaTopologicalInvariance Sheaf.Paper.UnboundedBaseChangeExtension Sheaf.Paper.VaryingRingGraphSummand Sheaf.Paper.VerdierCoefficientRealization Sheaf.Paper.VerdierExchange Sheaf.Paper.WeilChosenDualityExchange Sheaf.Paper.WeilCohomologyScalarExtensionQlbar Sheaf.PoincareDuality.ConstructibleSheafBiduality Sheaf.PoincareDuality.ProperProjectionFormulaBounded Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction Sheaf.SecSmoothPurity.FiniteGeneralRing Sheaf.SecSmoothPurity.MixedBaseChange Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization Sheaf.SecSmoothPurity.PurityDncCoefficientTransport Sheaf.SecSmoothPurity.Reduction Sheaf.SecSmoothPurity.ReductionCompatibilities Sheaf.SecSmoothPurity.ReductionDirectImage Sheaf.SecSmoothPurity.ReductionExceptional Sheaf.SecSmoothPurity.RestrictionTransitionTranspose Sheaf.SixFunctors.CoefDualFormulaScalarTranspose Sheaf.SixFunctors.CoefFinitePairingEvaluationData Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData Sheaf.SixFunctors.CoefIntegralFiniteExtension Sheaf.SixFunctors.CoefPairingFiniteNormalization Sheaf.SixFunctors.CoefPairingSystemDinaturality Sheaf.SixFunctors.CoefQbarVerdier Sheaf.SixFunctors.CoefSystemProjectionEvaluation Sheaf.SixFunctors.CoefTowerEvaluationPairing Sheaf.SixFunctors.CoefTowerNaturalCurrying Sheaf.SixFunctors.CoefTowerTraceRectification Sheaf.SixFunctors.CoefVerdierWeilEquivariance Sheaf.SixFunctors.CoefficientProjectionPointData Sheaf.SixFunctors.CompactSupportRefinementBaseChange Sheaf.SixFunctors.CtfStabilityDirectImages Sheaf.SixFunctors.DetSfCompBaseChangeDefs Sheaf.SixFunctors.DetSfCompCompositionBaseChange Sheaf.SixFunctors.DualizingSupportEvaluation Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization Sheaf.SixFunctors.FiniteAdjunctionSystemData Sheaf.SixFunctors.FiniteAdjunctionTransition Sheaf.SixFunctors.FiniteCoefficientVerdier Sheaf.SixFunctors.FiniteCounitRestrictionSquare Sheaf.SixFunctors.FiniteDualizing Sheaf.SixFunctors.FiniteExceptional Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds Sheaf.SixFunctors.FiniteMappingAdjunction Sheaf.SixFunctors.FiniteScalarMateData Sheaf.SixFunctors.FiniteScalarMateRealization Sheaf.SixFunctors.IntegralAffinePurityInduction Sheaf.SixFunctors.IntegralBrownAdjoint Sheaf.SixFunctors.IntegralComplementFiniteness Sheaf.SixFunctors.IntegralDualExceptionalSystem Sheaf.SixFunctors.IntegralDualizing Sheaf.SixFunctors.IntegralExceptionalAffineChart Sheaf.SixFunctors.IntegralExceptionalAffineFactorization Sheaf.SixFunctors.IntegralExceptionalDescendedCounit Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction Sheaf.SixFunctors.IntegralExceptionalMappingSystem Sheaf.SixFunctors.IntegralExceptionalRestriction Sheaf.SixFunctors.IntegralLocalizingCompactSupport Sheaf.SixFunctors.IntegralProjectiveLineAdjunction Sheaf.SixFunctors.IntegralRestrictionBoundedDescent Sheaf.SixFunctors.IntegralRestrictionChartCover Sheaf.SixFunctors.IntegralRestrictionClosed Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent Sheaf.SixFunctors.IntegralRestrictionFunctors Sheaf.SixFunctors.IntegralRestrictionGlue Sheaf.SixFunctors.IntegralRestrictionLine Sheaf.SixFunctors.IntegralTateLineConstructible Sheaf.SixFunctors.IntegralVerdier Sheaf.SixFunctors.IntegralVerdierModels Sheaf.SixFunctors.IntegralVerdierReductionPairing Sheaf.SixFunctors.IntegralVerdierSignedCalculus Sheaf.SixFunctors.NormalizedTowerTensorEvaluation Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction Sheaf.SixFunctors.ProperImageLocalizingProper Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose Sheaf.SixFunctors.RationalOperations Sheaf.SixFunctors.RationalRetractEvaluation Sheaf.SixFunctors.RationalVerdier Sheaf.SixFunctors.ScalarCompositeModelPasting Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare Sheaf.SixFunctors.ScalarRefinementClosureSquare Sheaf.SixFunctors.ScalarSixCompactSupport Sheaf.SixFunctors.ScalarSixCtf Sheaf.SixFunctors.ScalarSixDirectImage Sheaf.SixFunctors.WeilChosenDualityHom Sheaf.SmoothPurity.NormalizedWitness Sheaf.Targets.AffineSpaceRationalLine Sheaf.Targets.PoincareUncurry Sheaf.Targets.SmoothPurityQbar Sheaf.ZetaWeil.WeightPurityRoots TargetsCheck WeilConjectures WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights WeilConjectures.DeligneLaumon.AffineLine.Concentration WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound WeilConjectures.DeligneLaumon.AffineLine.DegreeOne WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional WeilConjectures.DeligneLaumon.AffineLine.Exactness WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport WeilConjectures.DeligneLaumon.AffineLine.FourierWeight WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension WeilConjectures.DeligneLaumon.AffineLine.Perverse WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform WeilConjectures.DeligneLaumon.AffineLine.Purity WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy WeilConjectures.DeligneLaumon.AffineLine.Upper WeilConjectures.DeligneLaumon.AffineLine.UpperReduction WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension WeilConjectures.DeligneLaumon.Reduction.AffineCurve WeilConjectures.DeligneLaumon.Reduction.DirectImage WeilConjectures.DeligneLaumon.Reduction.MixedStalk WeilConjectures.DeligneLaumon.Reduction.OpenLine WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed WeilConjectures.DeligneLaumon.Reduction.RealCurve WeilConjectures.DeligneLaumon.Reduction.RealSheaves WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary WeilConjectures.PoincareDuality.Poincare WeilConjectures.PoincareDuality.ProjectionFormula WeilConjectures.PoincareDuality.Verdier WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek WeilConjectures.SmoothPurity.Defs WeilConjectures.Statement WeilConjectures.TraceFormula.Additivity WeilConjectures.TraceFormula.BaseChangeCoherence WeilConjectures.TraceFormula.Basic WeilConjectures.TraceFormula.BorelMoore WeilConjectures.TraceFormula.CoefficientMorphism WeilConjectures.TraceFormula.CompactCohomology WeilConjectures.TraceFormula.CompactPullback WeilConjectures.TraceFormula.Correspondence WeilConjectures.TraceFormula.CorrespondencePair WeilConjectures.TraceFormula.CurvePieces WeilConjectures.TraceFormula.Dualizing WeilConjectures.TraceFormula.FibreCoherence WeilConjectures.TraceFormula.FibreModel WeilConjectures.TraceFormula.FixedPoint WeilConjectures.TraceFormula.FixedPointScheme WeilConjectures.TraceFormula.Frobenius WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite WeilConjectures.TraceFormula.FrobeniusLocalTerm WeilConjectures.TraceFormula.GenericQuotient WeilConjectures.TraceFormula.HomologyUnit WeilConjectures.TraceFormula.KunnethVerdier WeilConjectures.TraceFormula.LefschetzVerdier WeilConjectures.TraceFormula.LocalTerm WeilConjectures.TraceFormula.LocalTermLocality WeilConjectures.TraceFormula.Main WeilConjectures.TraceFormula.ModelExtension WeilConjectures.TraceFormula.OpenPieceCoherence WeilConjectures.TraceFormula.OpenSquare WeilConjectures.TraceFormula.PointNormalization WeilConjectures.TraceFormula.Product WeilConjectures.TraceFormula.ProperCompatibility WeilConjectures.TraceFormula.ProperCurve WeilConjectures.TraceFormula.ProperPushforward WeilConjectures.TraceFormula.ProperPushforwardKernel WeilConjectures.TraceFormula.PullbackFamily WeilConjectures.TraceFormula.RelativeFrobenius WeilConjectures.TraceFormula.RelativeFrobeniusComparison WeilConjectures.TraceFormula.RelativeFrobeniusIterate WeilConjectures.TraceFormula.ShriekTraceFunction WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage WeilConjectures.TraceFormula.ShriekTraceFunctionInduction WeilConjectures.TraceFormula.Stalk WeilConjectures.TraceFormula.Statement WeilConjectures.TraceFormula.SupportedPairing WeilConjectures.TraceFormula.TraceClass WeilConjectures.TraceFormula.TraceClassAdditivity WeilConjectures.TraceFormula.WeilBaseChange WeilConjectures.TraceFormula.WeilSheafUpperStar WeilConjectures.TraceFormula.WeilTrace WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek WeilConjectures.WeilSheaf.Curve WeilConjectures.WeilSheaf.EulerProduct WeilConjectures.WeilSheaf.LFunction WeilConjectures.WeilSheaf.RealPurity WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity WeilConjectures.ZetaFunction.BettiSymmetry WeilConjectures.ZetaFunction.CohomologicalFamily WeilConjectures.ZetaFunction.DualityReciprocity WeilConjectures.ZetaFunction.Examples WeilConjectures.ZetaFunction.ExamplesCohomology WeilConjectures.ZetaFunction.FinalTheorems WeilConjectures.ZetaFunction.HasseWeil WeilConjectures.ZetaFunction.IntegralFactors WeilConjectures.ZetaFunction.IntegralFrobeniusFactors WeilConjectures.ZetaFunction.LissePurity WeilConjectures.ZetaFunction.Rationality WeilConjectures.ZetaFunction.RealizationIndependence WeilConjectures.ZetaFunction.RelativePurity WeilConjectures.ZetaFunction.SmoothProper WeilConjectures.ZetaFunction.TraceFormula WeilConjectures.ZetaFunction.WeightSeparation WeilConjectures.ZetaFunction.Weights WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed | Same public declarations and definition bodies through the public data import; no adaptation. |

## Status

landed 20261025T101103-L-3656596 2026-10-25 (merge of deliver/G4/Sheaf.Paper.FiniteModelSheafQuotientConstructible)
