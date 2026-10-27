# Common-stage internal Hom data extraction

## Reason

The single-extension transport obligation must refer to the existing literal Hom
objects and comparisons. Extract these data into a new module to avoid an import
cycle with the item theorem that constructs the descended functor. This is a
source relocation: the nine public declaration commands below are textually
identical, including their signatures and definition bodies. The item publicly
re-exports both new data modules and the pullback proof module, and retains
every previous public import. The
existing private generic helper names and signatures used by `import all`
consumers remain in the item. Two complete generic proof implementations are
extracted into proof-support modules; their original private statements remain
as wrappers. The raw comparison uses its existing pure-tensor composition API,
keeping composition abstract locally. These proof changes introduce zero holes.
The two literal pullback definitions and their two existing complete comparison/descent
proofs are also extracted into CommonStagePullbackData and CommonStagePullbackDescent.
The original two public theorem names and signatures are publicly re-exported
from the support module. This further
split addresses the measured artifact-serialization compile time.
No coefficient category, permitted-pair predicate, chosen isomorphism, exported attribute,
universe, or target statement changes.

## Old

The following commands were declared in
`Sheaf.Paper.DerivedPullbackTensorHom`:

```lean
def operationStageTransitionIso (W : Scheme.{u})
    (E L : Index l Ω) (h : E ≤ L) :
    (stageSystem l Ω W).T h ≅ transition l Ω W E L h :=
  eqToIso ((stageSystem_existsUnique l Ω W).exists.choose_spec.1 E L h)
```

```lean
def commonStageHomPairs (W : Scheme.{u}) :
    ObjectProperty ((generalAlgebraicallyClosedConstructibleCategory l Ω W)ᵒᵖ ×
      generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  fun P ↦ constructibleRationalHomPairs l
    (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω P.1.unop.stage P.2.stage)) W
    (op (P.1.unop.toStage
      ((Padic.finiteCoefficientFields_properties l Ω).1 P.1.unop.stage P.2.stage).1),
      P.2.toStage
        ((Padic.finiteCoefficientFields_properties l Ω).1 P.1.unop.stage P.2.stage).2)
```

```lean
def commonStageHomRationalPair (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory) :
    (constructibleRationalHomPairs l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω
        P.obj.1.unop.stage P.obj.2.stage)) W).FullSubcategory :=
  ⟨(op (P.obj.1.unop.toStage
      ((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1),
    P.obj.2.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
      P.obj.1.unop.stage P.obj.2.stage).2), P.property⟩
```

```lean
def commonStageHomObject (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory) :
    generalAlgebraicallyClosedConstructibleCategory l Ω W :=
  ⟨Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage,
    (rationalDerivedInternalHom l (Coefficient.{u} l Ω
      (Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage)) W).obj
        (commonStageHomRationalPair l Ω W P)⟩
```

```lean
theorem commonStageHomPairAtStage_permitted (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    constructibleRationalHomPairs l (Coefficient.{u} l Ω L) W
      (op (P.obj.1.unop.toStage
        (((Padic.finiteCoefficientFields_properties l Ω).1
          P.obj.1.unop.stage P.obj.2.stage).1.trans h)),
        P.obj.2.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
          P.obj.1.unop.stage P.obj.2.stage).2.trans h)) := by
  let M := Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage
  have hM := (Padic.finiteCoefficientFields_properties l Ω).1
    P.obj.1.unop.stage P.obj.2.stage
  let A := Coefficient.{u} l Ω M
  let B := Coefficient.{u} l Ω L
  let e₁ := operationStageIntegralAssociator l Ω W P.obj.1.unop M L hM.1 h
  let e₂ := operationStageIntegralAssociator l Ω W P.obj.2 M L hM.2 h
  have hP := integralHomScalarPair_permitted l A B
    (coefficientInclusion l Ω M L h) W
      (integralPairOfRationalHomPair l A W (commonStageHomRationalPair l Ω W P))
  let e := (integralDerivedInternalHom l B W).mapIso
    (Iso.prod ((sfIntegralConstructible l B W).ι.mapIso e₁).symm.op
      ((sfIntegralConstructible l B W).ι.mapIso e₂))
  exact (sfIntegralConstructible l B W).prop_of_iso e hP
```

```lean
def commonStageHomPairAtStage (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    (constructibleRationalHomPairs l (Coefficient.{u} l Ω L) W).FullSubcategory :=
  ⟨(op (P.obj.1.unop.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans h)),
    P.obj.2.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
      P.obj.1.unop.stage P.obj.2.stage).2.trans h)),
    commonStageHomPairAtStage_permitted l Ω W P L h⟩
```

```lean
def commonStageHomComparison (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    (commonStageHomObject l Ω W P).toStage h ≅
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).obj
        (commonStageHomPairAtStage l Ω W P L h) :=
  (operationStageTransitionIso l Ω W _ L h).app
      (commonStageHomObject l Ω W P).obj ≪≫
    rationalHomScalarComparison l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω
        P.obj.1.unop.stage P.obj.2.stage))
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω _ L h) W
        (commonStageHomRationalPair l Ω W P) ≪≫
    (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).mapIso
      (ObjectProperty.isoMk _ (Iso.prod
        (((operationStageTransitionIso l Ω W _ L h).app
            (P.obj.1.unop.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
              P.obj.1.unop.stage P.obj.2.stage).1)).symm ≪≫
          ((stageSystem l Ω W).assoc ((Padic.finiteCoefficientFields_properties l Ω).1
            P.obj.1.unop.stage P.obj.2.stage).1 h).app P.obj.1.unop.obj).symm.op
        (((operationStageTransitionIso l Ω W _ L h).app
            (P.obj.2.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
              P.obj.1.unop.stage P.obj.2.stage).2)).symm ≪≫
          ((stageSystem l Ω W).assoc ((Padic.finiteCoefficientFields_properties l Ω).1
            P.obj.1.unop.stage P.obj.2.stage).2 h).app P.obj.2.obj)))
```


```lean
def commonStagePullbackObject {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  ⟨P.stage, (rationalDerivedPullback l (Coefficient.{u} l Ω P.stage) f).obj P.obj⟩
```


```lean
def commonStagePullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : Index l Ω) (h : P.stage ≤ L) :
    (commonStagePullbackObject l Ω f P).toStage h ≅
      (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).obj (P.toStage h) :=
  (operationStageTransitionIso l Ω X P.stage L h).app
      (commonStagePullbackObject l Ω f P).obj ≪≫
    (rationalPullbackScalarComparison l (Coefficient.{u} l Ω P.stage)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω P.stage L h) f).app P.obj ≪≫
    (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).mapIso
      ((operationStageTransitionIso l Ω Y P.stage L h).app P.obj).symm
```

## New

The following identical commands are declared in
`Sheaf.Paper.CommonStageInternalHomData` (the first seven) and
`Sheaf.Paper.CommonStagePullbackData` (the last two), both publicly imported by the item:

```lean
def operationStageTransitionIso (W : Scheme.{u})
    (E L : Index l Ω) (h : E ≤ L) :
    (stageSystem l Ω W).T h ≅ transition l Ω W E L h :=
  eqToIso ((stageSystem_existsUnique l Ω W).exists.choose_spec.1 E L h)
```

```lean
def commonStageHomPairs (W : Scheme.{u}) :
    ObjectProperty ((generalAlgebraicallyClosedConstructibleCategory l Ω W)ᵒᵖ ×
      generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  fun P ↦ constructibleRationalHomPairs l
    (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω P.1.unop.stage P.2.stage)) W
    (op (P.1.unop.toStage
      ((Padic.finiteCoefficientFields_properties l Ω).1 P.1.unop.stage P.2.stage).1),
      P.2.toStage
        ((Padic.finiteCoefficientFields_properties l Ω).1 P.1.unop.stage P.2.stage).2)
```

```lean
def commonStageHomRationalPair (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory) :
    (constructibleRationalHomPairs l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω
        P.obj.1.unop.stage P.obj.2.stage)) W).FullSubcategory :=
  ⟨(op (P.obj.1.unop.toStage
      ((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1),
    P.obj.2.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
      P.obj.1.unop.stage P.obj.2.stage).2), P.property⟩
```

```lean
def commonStageHomObject (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory) :
    generalAlgebraicallyClosedConstructibleCategory l Ω W :=
  ⟨Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage,
    (rationalDerivedInternalHom l (Coefficient.{u} l Ω
      (Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage)) W).obj
        (commonStageHomRationalPair l Ω W P)⟩
```

```lean
theorem commonStageHomPairAtStage_permitted (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    constructibleRationalHomPairs l (Coefficient.{u} l Ω L) W
      (op (P.obj.1.unop.toStage
        (((Padic.finiteCoefficientFields_properties l Ω).1
          P.obj.1.unop.stage P.obj.2.stage).1.trans h)),
        P.obj.2.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
          P.obj.1.unop.stage P.obj.2.stage).2.trans h)) := by
  let M := Padic.finiteCoefficientCompositum l Ω P.obj.1.unop.stage P.obj.2.stage
  have hM := (Padic.finiteCoefficientFields_properties l Ω).1
    P.obj.1.unop.stage P.obj.2.stage
  let A := Coefficient.{u} l Ω M
  let B := Coefficient.{u} l Ω L
  let e₁ := operationStageIntegralAssociator l Ω W P.obj.1.unop M L hM.1 h
  let e₂ := operationStageIntegralAssociator l Ω W P.obj.2 M L hM.2 h
  have hP := integralHomScalarPair_permitted l A B
    (coefficientInclusion l Ω M L h) W
      (integralPairOfRationalHomPair l A W (commonStageHomRationalPair l Ω W P))
  let e := (integralDerivedInternalHom l B W).mapIso
    (Iso.prod ((sfIntegralConstructible l B W).ι.mapIso e₁).symm.op
      ((sfIntegralConstructible l B W).ι.mapIso e₂))
  exact (sfIntegralConstructible l B W).prop_of_iso e hP
```

```lean
def commonStageHomPairAtStage (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    (constructibleRationalHomPairs l (Coefficient.{u} l Ω L) W).FullSubcategory :=
  ⟨(op (P.obj.1.unop.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans h)),
    P.obj.2.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
      P.obj.1.unop.stage P.obj.2.stage).2.trans h)),
    commonStageHomPairAtStage_permitted l Ω W P L h⟩
```

```lean
def commonStageHomComparison (W : Scheme.{u})
    (P : (commonStageHomPairs l Ω W).FullSubcategory)
    (L : Index l Ω) (h : (commonStageHomObject l Ω W P).stage ≤ L) :
    (commonStageHomObject l Ω W P).toStage h ≅
      (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).obj
        (commonStageHomPairAtStage l Ω W P L h) :=
  (operationStageTransitionIso l Ω W _ L h).app
      (commonStageHomObject l Ω W P).obj ≪≫
    rationalHomScalarComparison l
      (Coefficient.{u} l Ω (Padic.finiteCoefficientCompositum l Ω
        P.obj.1.unop.stage P.obj.2.stage))
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω _ L h) W
        (commonStageHomRationalPair l Ω W P) ≪≫
    (rationalDerivedInternalHom l (Coefficient.{u} l Ω L) W).mapIso
      (ObjectProperty.isoMk _ (Iso.prod
        (((operationStageTransitionIso l Ω W _ L h).app
            (P.obj.1.unop.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
              P.obj.1.unop.stage P.obj.2.stage).1)).symm ≪≫
          ((stageSystem l Ω W).assoc ((Padic.finiteCoefficientFields_properties l Ω).1
            P.obj.1.unop.stage P.obj.2.stage).1 h).app P.obj.1.unop.obj).symm.op
        (((operationStageTransitionIso l Ω W _ L h).app
            (P.obj.2.toStage ((Padic.finiteCoefficientFields_properties l Ω).1
              P.obj.1.unop.stage P.obj.2.stage).2)).symm ≪≫
          ((stageSystem l Ω W).assoc ((Padic.finiteCoefficientFields_properties l Ω).1
            P.obj.1.unop.stage P.obj.2.stage).2 h).app P.obj.2.obj)))
```


```lean
def commonStagePullbackObject {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  ⟨P.stage, (rationalDerivedPullback l (Coefficient.{u} l Ω P.stage) f).obj P.obj⟩
```


```lean
def commonStagePullbackComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : Index l Ω) (h : P.stage ≤ L) :
    (commonStagePullbackObject l Ω f P).toStage h ≅
      (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).obj (P.toStage h) :=
  (operationStageTransitionIso l Ω X P.stage L h).app
      (commonStagePullbackObject l Ω f P).obj ≪≫
    (rationalPullbackScalarComparison l (Coefficient.{u} l Ω P.stage)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω P.stage L h) f).app P.obj ≪≫
    (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).mapIso
      ((operationStageTransitionIso l Ω Y P.stage L h).app P.obj).symm
```

## Users

`tools/downstream.py Sheaf.Paper.DerivedPullbackTensorHom --uses commonStageHomComparison`
finds 11 modules with occurrences, including the item. The table is the union of
occurrences of all seven moved names, found by `rg -l -w` in both library roots.
The original module had 274 direct importers at the initial source inspection; their public interface is preserved.
No existing module besides the item is edited. This inventory predates the shared
build quarantine at 2026-10-27T12:30:24Z: consumers moved to quarantine keep the
same declaration contract, and their archives are not changed or withdrawn by
this delivery. Consumer compilation uses active files only.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.AdicAmbientHomEvaluationComparison` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.AdicCommonStageHomTranspose` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.AdicHomTensorLisseCriterion` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.AdicLisseLinearDualComparisons` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.AdicRealizationFamilyData` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.AdicReindexingHom` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.AdmissibleHomSubstitution` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CanonicalTateCommonComparisons` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.ClopenExceptionalScalarDescent` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CoefficientDualModelTransport` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CoherentRationalPullbackIdentity` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CommonProjectionOpenFactor` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CommonProjectionOpenPullbackTensor` | J7 | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CommonStageEvaluationNaturality` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CommonStageFiniteObjectLifting` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CommonStageInclusionTensorComparison` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CommonStageInclusionTensorModel` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CommonStageInclusionTensorNaturality` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CommonStageOpenHeartAdjunction` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CommonStagePullbackNormalizedDescent` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CommonStageRestrictionTensorDescent` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CommonStageTensorLineCoherenceNaturality` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CommonStageTensorRightUnitorNaturality` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CommonTensorBraidingNaturality` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.ConstructibleMateCoherence` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.ConstructiblePullbackTExact` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.CtfCoefficientStageSelectors` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.DerivedPullbackTensorHom` | E3 | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.DerivedPullbackTensorIso` | J2 | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.ExceptionalCommonStageDescent` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.FiniteProductFieldCoefficientDescent` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.FrobeniusEvaluationProjectionCoherence` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.FrobeniusSquareExchange` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.IsomorphismFieldTransportEpsilonNaturality` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.IsomorphismFieldTransportShiftDescent` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.LisseCohomologyDerivedDual` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.LisseShortComplexCommonStageExactness` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.MixedCupFieldOperations` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.MixedCupTensorClosure` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.NativeAdicRealizationData` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.NormalizedCommonEvaluationForStructure` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.NormalizedCommonEvaluationNaturality` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.NormalizedOrientationPerfectDuality` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.OpenWeilCoefficientFibres` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.OperationCoefficientActionData` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.OrientationCoefficientTwists` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.PodReindexingHomCoefficientDescent` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.PoincareDualityConventions` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.PuritySourceTransports` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.RestrictionTensorRepresentativeTransport` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.SemilinearFieldOperationLifts` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.SfNormalizedCommonStageWeilSquares` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.SfPackageCoefficientDomains` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.SfPackageFieldOperationRealization` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.SfPackageQbarAdjunctionMapDescent` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.SfQbarLocalizationCommonStage` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.SfQbarLocalizationFiniteCoherence` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.SfQbarLocalizationFiniteData` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.SixFunctorDatum` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.SmoothOperationCoefficientComparisons` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.TensorHomExchange` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.VerdierPairingThreeTransposes` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.WeilChosenDualityExchangeData` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.Paper.ZlOpenWeilUnitEmptyFibre` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdierData` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.SixFunctors.CoefQbarVerdierInternalHom` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyComparisonFactors` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyRationalCocycle` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyRealization` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyRealizationTransport` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.SixFunctors.TensorExchangePresentation` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.SixFunctors.WeilChosenDualityHom` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.WeilSheaf.DualRealizationComparison` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.WeilSheaf.NativeDualRealizationComparisonData` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |
| `Sheaf.WeilSheaf.StructuralOmegaHomPairs` | unclaimed | Same declaration signatures, bodies and public availability; no adaptation. |

Additional pullback-definition consumers, inventoried 2026-10-27 after the
existing Hom inventory (quarantined source is preserved):

| Module | Holder | Effect |
| --- | --- | --- |
| `Sheaf.Paper.AutomorphismConstructibleStageEquivalence` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.CommonStageFiniteHomLifting` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.CommonStagePointReturn` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.CommonStagePullbackIdentity` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.CommonStagePullbackRepresentativeLinearity` | G1 | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | B2 | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.ConstantExtensionSheetHeartData` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.DlLocallyConstructibleAdicHeart` | D4 | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.FdCoefficientComparisonSystem` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.FdCommonStageComparisonDescent` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.FdNormalizedPullbackMixed` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.FdScalarRoosComparisonIntertwining` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.FiniteGeometricSectionsPointOrbits` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.FrobeniusPullbackOrdinaryExchange` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.IsomorphismFieldTransportClauses` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.IsomorphismFieldTransportCommonStage` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.PointRationalFamilyCommonStageNaturality` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.ProperSupportCoefficientAdjunction` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.PurityKappaStages` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.SfCommonStageDirectImage` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.SfCommonStageLocalizationConstruction` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.SfRationalDirectImageAdjunction` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.ZlFrameworkPbcOpenComparisonData` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.ZlOpenCompactSupportRestriction` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.Paper.ZlSfPbcNormalizedHeartModel` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.SixFunctors.KappaCoefficientCoherence` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |
| `Sheaf.SixFunctors.KappaGeometricComparisons` | unclaimed | Same literal pullback definitions, signatures and public availability; no adaptation. |

The two `import all` consumers `FiniteProductFieldCoefficientDescent` and
`RationalRestrictionComparisonCoherence` retain the private generic helpers in the
original item. The extraction changes no definition's exported transparency attribute.

Validation: all eight delivery modules compiled with artifact generation. The
unchanged direct importers RationalRestrictionComparisonCoherence (using the
private generic API) and CommonStagePullbackNormalizedDescent (using the public
pullback API) compiled against the delivery. Their temporary copies were removed.

FiniteProductFieldCoefficientDescent exceeded the limit without a type error
against the delivery (104 seconds) and also against the published library in a
separate baseline sandbox (90 seconds). This existing timing problem is reported;
its source and archive are not edited or withdrawn. All temporary consumer and
baseline files were removed.

The two relocated pullback lemma nodes now record CommonStagePullbackData as a
statement dependency, matching the public definitions used by their unchanged
signatures. Their mathematical statements and global declaration names are kept.

## Status

landed 20261027T233908-L-4133266 2026-10-27 (merge of deliver/E3/Sheaf.Paper.DerivedPullbackTensorHom)
