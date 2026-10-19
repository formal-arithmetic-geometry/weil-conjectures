# WeilConjectures.PurityFiniteSetting.gysinHomToSections and Gysin evaluation definitions

## Reason

The complete original interface and proof exceed the server's 60-second file limit.
Profiling isolated repeated kernel conversions between specialized derived functor object
projections. The repairs retain exactly the existing constructions: name the ordinary
functor object projection, perform derived evaluation, global-class evaluation, coefficient
comparison composition, and class transport over abstract categories, then specialize them.
No witness is chosen and no theorem is assumed by any definition. The object abbreviations
`gysinEtaleInput`, `gysinInput`, `gysinClosed`, `gysinValue`, and `gysinSupport` are unchanged.

All six old definitions below have definitionally identical values and types: the new
helpers merely factor their original applications/compositions. In particular the canonical
forward coefficient map, the actual coordinate Kummer class, the shift comparison and the
normalization equation are retained. Public function binders are preserved; the named
object wrappers reduce to the old objects. `gysin_structure` has its full original signature.
Targets are not textually changed and their meanings are unchanged; the usual independent
reading of target definitions still applies to this recorded definition repair.

New public implementation helpers in the same module are `gysinFunctorObj`,
`gysinDerivedEvaluate`, `gysinDerivedGlobalClass`, `gysinCoefficientComposite`, and
`gysinTransportClass`. Their bodies are explicit constructions with no `sorry`.
`open CategoryTheory.Abelian` makes `HasKInjectiveResolutions` available in the general API;
no existing public import or visibility is changed.

## Old

```lean
def gysinEvaluate (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {F : ProSheaves P T} (f : P.constant T ⟶ F) :
    (globalSectionsFunctor (Modules P) T).obj F :=
  ((constantSheafAdj T.smallEtaleTopology (Modules P)
    (Scheme.Etale.isTerminalMkId T)).homEquiv _ _
      ((comparisonAdjunction (Modules P) T).homEquiv _ _ f)) 1

def gysinHomToSections (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (m : P.derivedSheaf h Y false ⟶ P.gysinValue h Y) :
    (localClasses P Y 0).obj (P.gysinValue h Y) :=
  P.gysinEvaluate Y
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ProSheaves P Y) 0).inv.app
      (P.constant Y) ≫ (DerivedCategory.homologyFunctor (ProSheaves P Y) 0).map m)

def gysinGlobalClass (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {K : DerivedCategory (ProSheaves P T)} (q : ℤ)
    (m : (DerivedCategory.singleFunctor (ProSheaves P T) 0).obj (P.constant T) ⟶ K⟦q⟧) :
    (hyper P T q).obj K :=
  let E := globalSectionsFunctor (Modules P) T
  let v := (E.homologyRightDerivedFunctorObjSingleFunctorIso (P.constant T) 0).inv
    ((E.toRightDerivedZero.app (P.constant T)) (P.gysinEvaluate T (𝟙 (P.constant T))))
  ((DerivedCategory.homologyFunctor (Modules P) 0).map
      (E.rightDerivedFunctor.map m ≫
        (E.rightDerivedFunctor.commShiftIso q).hom.app K) ≫
    ((DerivedCategory.homologyFunctor (Modules P) 0).shiftIso q 0 q (add_zero q)).hom.app
      (E.rightDerivedFunctor.obj K)) v

def gysinOpenCoefficient (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :
    (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory.obj
        (P.gysinInput h Y).obj ⟶ P.derivedSheaf h (Punctured Y) true :=
  let j := openImmersion Y
  let V := upperStar (Modules P) j
  V.mapDerivedCategory.map
    (((comparisonUpperStar (Modules P) (Line Y)).mapDerivedCategorySingleFunctor 0).hom.app
      (P.twistEtale h (Line Y))) ≫
    (V.mapDerivedCategorySingleFunctor 0).hom.app (P.twist h (Line Y)) ≫
    (DerivedCategory.singleFunctor (ProSheaves P (Punctured Y)) 0).map
      ((comparisonUpperStarCompUpperStarIso (Modules P) j).hom.app
        (P.twistEtale h (Line Y)) ≫
        (comparisonUpperStar (Modules P) (Punctured Y)).map (P.twistEtalePullback h j))

def gysinKummerSection (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (c : Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y))
    (b : (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory.obj
      (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true) :
    (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology (Line Y)) (Modules P)
      (Scheme.ProEt.mk (zeroSection Y).openComplement.ι) 1).obj (P.gysinInput h Y) :=
  let j := openImmersion Y
  let V := upperStar (Modules P) j
  let E := globalSectionsFunctor (Modules P) (Punctured Y)
  letI := (openImmersionLowerShriekUpperStarAdjunction (Modules P) j).preservesKInjectiveComplexes
  let e := Functor.isoWhiskerRight V.rightDerivedFunctorIsoMapDerivedCategory.symm
      E.rightDerivedFunctor ≪≫
    Functor.rightDerivedFunctorCompIso' V E (openSectionsIso P j)
  let x := (DerivedCategory.homologyFunctor (Modules P) 1).map
    (E.rightDerivedFunctor.map b.inv ≫ e.hom.app (P.gysinInput h Y).obj)
      (P.gysinGlobalClass (Punctured Y) 1 (P.coordinateKummer h Y a).hom)
  let y := ((sectionPlusIso P (Line Y) (Scheme.ProEt.mk j) 1).hom.app
    (P.gysinInput h Y)) x
  ((complementSectionsIso P (zeroSection Y) j c.complement 1).hom.app
    (P.gysinInput h Y)) y

def GysinSupportIdentification (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  Nonempty (Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)) ∧
  ∀ c : Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y),
    ∃ (b : (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory.obj
          (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true)
      (edge : (hyper P Y 2).obj (P.gysinClosed h Y) ≅
        (localClasses P Y 2).obj (P.gysinClosed h Y))
      (e : (localClasses P Y 0).obj (P.gysinValue h Y) ≅ P.gysinSupport h Y),
      b.hom = P.gysinOpenCoefficient h Y ∧
      edge.hom = (c.edge 2).app (P.gysinClosed h Y) ∧
      e.hom = (globalSectionsFunctor (Modules P) Y).map
          (((DerivedCategory.homologyFunctor (ProSheaves P Y) 0).shiftIso
            (2 : ℤ) 0 2 (add_zero 2)).hom.app (P.gysinClosed h Y)) ≫
        edge.inv ≫ (c.supportIso 2).hom.app (P.gysinEtaleInput h Y) ∧
      ∀ δ : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology (Line Y)) (Modules P)
          (supportRestrictionArrow (zeroSection Y)) ⊤,
        Sheaf.SupportSequenceExact (Scheme.ProEt.topology (Line Y)) (Modules P)
          (supportRestrictionArrow (zeroSection Y)) ⊤ δ →
        ∃ m : P.derivedSheaf h Y false ⟶ P.gysinValue h Y,
          e.hom (P.gysinHomToSections h Y m) =
            (δ 1).app ⟨P.gysinInput h Y, trivial⟩ (P.gysinKummerSection h Y a c b)
```

## New

```lean
def gysinEvaluate (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {F : ProSheaves P T} (f : P.constant T ⟶ F) :
    gysinFunctorObj (D := Modules P) (globalSectionsFunctor (Modules P) T) F :=
  ((constantSheafAdj T.smallEtaleTopology (Modules P)
    (Scheme.Etale.isTerminalMkId T)).homEquiv _ _
      ((comparisonAdjunction (Modules P) T).homEquiv _ _ f)) 1

def gysinHomToSections (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (m : gysinFunctorObj (DerivedCategory.singleFunctor (ProSheaves P Y) 0)
      (P.constant Y) ⟶ P.gysinValue h Y) :
    gysinFunctorObj (D := Modules P) (localClasses P Y 0) (P.gysinValue h Y) :=
  gysinDerivedEvaluate (globalSectionsFunctor (Modules P) Y) (P.constant Y)
    (P.gysinValue h Y) (fun F ↦ P.gysinEvaluate Y (F := F)) m

def gysinGlobalClass (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {K : DerivedCategory (ProSheaves P T)} (q : ℤ)
    (m : gysinFunctorObj (DerivedCategory.singleFunctor (ProSheaves P T) 0) (P.constant T) ⟶
      gysinFunctorObj (shiftFunctor (DerivedCategory (ProSheaves P T)) q) K) :
    gysinFunctorObj (D := Modules P) (hyper P T q) K :=
  gysinDerivedGlobalClass P.Coefficient (globalSectionsFunctor (Modules P) T)
    (P.constant T) q m (P.gysinEvaluate T (𝟙 (P.constant T)))

def gysinOpenCoefficient (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :
    gysinFunctorObj (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory
        (P.gysinInput h Y).obj ⟶ P.derivedSheaf h (Punctured Y) true :=
  gysinCoefficientComposite
    (DerivedCategory.singleFunctor (EtSheaves P (Line Y)) 0)
    (DerivedCategory.singleFunctor (ProSheaves P (Line Y)) 0)
    (DerivedCategory.singleFunctor (ProSheaves P (Punctured Y)) 0)
    (upperStar (Modules P) (openImmersion Y))
    (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory
    (comparisonUpperStar (Modules P) (Line Y))
    (comparisonUpperStar (Modules P) (Line Y)).mapDerivedCategory
    ((comparisonUpperStar (Modules P) (Line Y)).mapDerivedCategorySingleFunctor 0).hom
    ((upperStar (Modules P) (openImmersion Y)).mapDerivedCategorySingleFunctor 0).hom
    (P.twistEtale h (Line Y)) (P.twist h (Punctured Y))
    ((comparisonUpperStarCompUpperStarIso (Modules P) (openImmersion Y)).hom.app
      (P.twistEtale h (Line Y)) ≫
      (comparisonUpperStar (Modules P) (Punctured Y)).map
        (P.twistEtalePullback h (openImmersion Y)))

def gysinKummerSection (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (c : Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y))
    (b : gysinFunctorObj (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory
      (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true) :
    gysinFunctorObj (D := Modules P)
    (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology (Line Y)) (Modules P)
      (Scheme.ProEt.mk (zeroSection Y).openComplement.ι) 1) (P.gysinInput h Y) :=
  let j := openImmersion Y
  let V := upperStar (Modules P) j
  let E := globalSectionsFunctor (Modules P) (Punctured Y)
  letI := (openImmersionLowerShriekUpperStarAdjunction (Modules P) j).preservesKInjectiveComplexes
  let e := Functor.isoWhiskerRight V.rightDerivedFunctorIsoMapDerivedCategory.symm
      E.rightDerivedFunctor ≪≫
    Functor.rightDerivedFunctorCompIso' V E (openSectionsIso P j)
  let x := gysinTransportClass V.mapDerivedCategory E.rightDerivedFunctor _
    (DerivedCategory.homologyFunctor (Modules P) 1) e (P.gysinInput h Y).obj
    (P.derivedSheaf h (Punctured Y) true)
    (P.gysinGlobalClass (Punctured Y) 1 (P.coordinateKummer h Y a).hom) b
  let y := ((sectionPlusIso P (Line Y) (Scheme.ProEt.mk j) 1).hom.app
    (P.gysinInput h Y)) x
  ((complementSectionsIso P (zeroSection Y) j c.complement 1).hom.app
    (P.gysinInput h Y)) y

def GysinSupportIdentification (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  Nonempty (Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)) ∧
  ∀ c : Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y),
    ∃ (b : gysinFunctorObj (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory
          (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true)
      (edge : gysinFunctorObj (D := Modules P) (hyper P Y 2) (P.gysinClosed h Y) ≅
        gysinFunctorObj (D := Modules P) (localClasses P Y 2) (P.gysinClosed h Y))
      (e : gysinFunctorObj (D := Modules P) (localClasses P Y 0)
        (P.gysinValue h Y) ≅ P.gysinSupport h Y),
      b.hom = P.gysinOpenCoefficient h Y ∧
      edge.hom = (c.edge 2).app (P.gysinClosed h Y) ∧
      e.hom = (globalSectionsFunctor (Modules P) Y).map
          (((DerivedCategory.homologyFunctor (ProSheaves P Y) 0).shiftIso
            (2 : ℤ) 0 2 (add_zero 2)).hom.app (P.gysinClosed h Y)) ≫
        edge.inv ≫ (c.supportIso 2).hom.app (P.gysinEtaleInput h Y) ∧
      ∀ δ : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology (Line Y)) (Modules P)
          (supportRestrictionArrow (zeroSection Y)) ⊤,
        Sheaf.SupportSequenceExact (Scheme.ProEt.topology (Line Y)) (Modules P)
          (supportRestrictionArrow (zeroSection Y)) ⊤ δ →
        ∃ m : gysinFunctorObj (DerivedCategory.singleFunctor (ProSheaves P Y) 0)
            (P.constant Y) ⟶ P.gysinValue h Y,
          e.hom (P.gysinHomToSections h Y m) =
            (δ 1).app ⟨P.gysinInput h Y, trivial⟩ (P.gysinKummerSection h Y a c b)
```

The five general helper definitions are in the delivered module immediately before their
specializations. Private proved lemmas transport concentration and constructibility through
an isomorphism and establish evaluation bijectivity; they are proof code, not new assumptions.

## Users

The source scan `tools/downstream.py Sheaf.Paper.PurityGysinStructure --uses` was run for
all ten existing object/evaluation names, including the unchanged object abbreviations.
The table inventories all 179 known consumers, conservatively including modules that
only import the interface. Direct textual consumers include the two orientation modules and the three
supported-stalk modules added since the initial scan. Their statements have definitionally identical types, so no consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | G4 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | E5 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | Direct consumer; see validation below; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | Direct consumer; see validation below; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportRestrictionZeroGerm | unclaimed | Definitionally identical evaluation interface; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Definitionally identical evaluation interface; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalkMap | unclaimed | Definitionally identical evaluation interface; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | R3 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | G3 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Definitionally identical operations and types; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Definitionally identical operations and types; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Definitionally identical operations and types; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Definitionally identical operations and types; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Definitionally identical operations and types; no adaptation. |
| TargetsCheck | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.Statement | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Definitionally identical operations and types; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Definitionally identical operations and types; no adaptation. |

Validation: all four delivered modules compiled together, without warnings. The unchanged
original `PurityAffineLineOrientation` (holder J6) compiled against the fresh main artifact
in 47.8 seconds. Original `PurityAffineLineOrientationUniqueness` (holder E2) exceeded the
60-second limit without a type error; it is not adapted and is not claimed as a passed
compile. The independent reader should repeat that consumer check. A whole-predicate
`rfl` probe exceeded the limit while elaborating the old expression; generic operation
bodies can be read directly to check their definitional equality.

## Status

landed 20261019T231136-L-552854 2026-10-19 (merge of deliver/F1/Sheaf.Paper.PurityGysinStructure)
