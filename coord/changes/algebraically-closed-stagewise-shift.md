# WeilConjectures.AlgebraicallyClosedCoefficients stagewise structures

## Reason

The cached stage instances name the same underlying structures directly. Local
opacity keeps elaboration from repeatedly expanding the completed coefficient
categories. The tensor associator is transported along equality of coefficient maps;
`correctedTensorAssociator_formula` proves equality with the original tensor formula.
The sealed associator specification fixes the entire isomorphism, including its inverse.

The original transported Hom group and preadditive construction are retained.
Private, proved equality comparisons identify them with the upstream quotient
structures and transfer the proved composition and additive-functor APIs. The
upstream preadditive module remains a proof-only import, preserving instance selection
in downstream modules. The shift and inclusion comparisons use the actual upstream
stagewise construction and its normalized identity components.

No target statement changes. Targets using the changed data receive the normal
statement-meaning review again. The associator equality and representative and
shift formulas supply the comparison certificates.

## Old

```lean
noncomputable def Stage (E : Index l Ω) :=
  rationalConstructibleCategory D l hl (Coefficient.{u} l Ω E) Y

noncomputable instance stageCategory (E : Index l Ω) :
    Category (Stage D l hl Ω Y E) :=
  inferInstanceAs (Category (rationalConstructibleCategory D l hl (Coefficient.{u} l Ω E) Y))

noncomputable instance stagePreadditive (E : Index l Ω) :
    Preadditive (Stage D l hl Ω Y E) :=
  inferInstanceAs (Preadditive
    (rationalConstructibleCategory D l hl (Coefficient.{u} l Ω E) Y))

noncomputable instance stageShift (E : Index l Ω) :
    HasShift (Stage D l hl Ω Y E) ℤ :=
  rationalConstructibleShift D l hl (Coefficient.{u} l Ω E) Y

noncomputable instance stagePretriangulated (E : Index l Ω) :
    Pretriangulated (Stage D l hl Ω Y E) :=
  rationalConstructiblePretriangulated D l hl (Coefficient.{u} l Ω E) Y

noncomputable def associator (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    transition D l hl Ω Y E L h ⋙ transition D l hl Ω Y L M k ≅
      transition D l hl Ω Y E M (h.trans k) :=
  rationalConstructibleScalarComp l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
    (coefficientInclusion l Ω E L h) Y (Coefficient.{u} l Ω M)
    (coefficientInclusion l Ω L M k) D hl ≪≫
    eqToIso (congrArg (rationalScalarExtension D l hl
      (Coefficient.{u} l Ω E) Y (Coefficient.{u} l Ω M))
      ((coefficientInclusion_laws l Ω).2 E L M h k))

noncomputable abbrev stageSystem : StageSystem (Stage D l hl Ω Y) :=
  (stageSystem_existsUnique D l hl Ω Y).exists.choose

noncomputable instance stageTransitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (stageTransition D l hl Ω Y E L h).CommShift ℤ :=
  cast (congrArg (fun F : Stage D l hl Ω Y E ⥤ Stage D l hl Ω Y L ↦ F.CommShift ℤ)
    ((stageSystem_existsUnique D l hl Ω Y).exists.choose_spec.1 E L h).symm)
    (transitionCommShift D l hl Ω Y E L h)

noncomputable instance pairCategory : Category (Pair D l hl Ω Y) :=
  inferInstanceAs (Category (stageSystem D l hl Ω Y).PairCategory)

noncomputable def StageHom (A B : Pair D l hl Ω Y) (L : Common A B) :=
  ((stageTransition D l hl Ω Y A.stage L.val L.property.1).obj A.obj ⟶
    (stageTransition D l hl Ω Y B.stage L.val L.property.2).obj B.obj)

noncomputable instance stageHomAddCommGroup (A B : Pair D l hl Ω Y) (L : Common A B) :
    AddCommGroup (StageHom A B L) :=
  inferInstanceAs (AddCommGroup
    ((stageTransition D l hl Ω Y A.stage L.val L.property.1).obj A.obj ⟶
      (stageTransition D l hl Ω Y B.stage L.val L.property.2).obj B.obj))

noncomputable def transport (A B : Pair D l hl Ω Y) (L M : Common A B) (h : L ≤ M)
    (f : StageHom A B L) : StageHom A B M :=
  ((stageSystem D l hl Ω Y).assoc L.property.1 h).inv.app A.obj ≫
    (stageTransition D l hl Ω Y L.val M.val h).map f ≫
    ((stageSystem D l hl Ω Y).assoc L.property.2 h).hom.app B.obj

noncomputable def transportHom (A B : Pair D l hl Ω Y) (L M : Common A B) (h : L ≤ M) :
    StageHom A B L →+ StageHom A B M where
  toFun := transport A B L M h
  map_zero' := (transport_additive A B L M h).1
  map_add' := (transport_additive A B L M h).2

noncomputable def ColimitHom (A B : Pair D l hl Ω Y) :=
  AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)

noncomputable instance colimitHomGroup (A B : Pair D l hl Ω Y) : AddCommGroup (ColimitHom A B) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)))

noncomputable instance homAddCommGroup (A B : Pair D l hl Ω Y) : AddCommGroup (A ⟶ B) :=
  (homCoordinates A B).addCommGroup

noncomputable instance preadditive : Preadditive (Pair D l hl Ω Y) where
  homGroup A B := homAddCommGroup A B
  add_comp A B C f f' g := composition_bilinear.1 A B C f f' g
  comp_add A B C f g g' := composition_bilinear.2 A B C f g g'

noncomputable instance hasShift : HasShift (Pair D l hl Ω Y) ℤ := shift_exists.choose

noncomputable instance shiftAdditive (n : ℤ) :
    (shiftFunctor (Pair D l hl Ω Y) n).Additive := shift_exists.choose_spec.1 n

noncomputable instance inclusionCommShift (E : Index l Ω) :
    (inclusion E : Stage D l hl Ω Y E ⥤ _).CommShift ℤ :=
  shift_exists.choose_spec.2.2.2.choose E
```

## New

```lean
noncomputable def Stage (E : Index l Ω) :=
  rationalConstructibleCategory D l hl (Coefficient.{u} l Ω E) Y

@[instance_reducible]
noncomputable instance stageCategory (E : Index l Ω) :
    Category (Stage D l hl Ω Y E) :=
  ScalarLocalization.category _ _ _

@[instance_reducible]
noncomputable instance stagePreadditive (E : Index l Ω) :
    Preadditive (Stage D l hl Ω Y E) :=
  ScalarLocalization.preadditive _ _ _

@[instance_reducible]
noncomputable instance stageShift (E : Index l Ω) :
    HasShift (Stage D l hl Ω Y E) ℤ :=
  rationalConstructibleShift D l hl (Coefficient.{u} l Ω E) Y

@[instance_reducible]
noncomputable instance stagePretriangulated (E : Index l Ω) :
    Pretriangulated (Stage D l hl Ω Y E) :=
  rationalConstructiblePretriangulated D l hl (Coefficient.{u} l Ω E) Y

noncomputable def associator (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M) :
    transition D l hl Ω Y E L h ⋙ transition D l hl Ω Y L M k ≅
      transition D l hl Ω Y E M (h.trans k) :=
  (associator_specification D l hl Ω Y E L M h k).exists.choose

noncomputable def stageSystem : StageSystem (Stage D l hl Ω Y) :=
  (stageSystem_existsUnique D l hl Ω Y).exists.choose

noncomputable instance stageTransitionCommShift (E L : Index l Ω) (h : E ≤ L) :
    (stageTransition D l hl Ω Y E L h).CommShift ℤ :=
  cast (congrArg (fun F : Stage D l hl Ω Y E ⥤ Stage D l hl Ω Y L ↦ F.CommShift ℤ)
    (stageSystem_transition D l hl Ω Y E L h).symm)
    (transitionCommShift D l hl Ω Y E L h)

@[instance_reducible]
noncomputable instance pairCategory : Category (Pair D l hl Ω Y) :=
  StageSystem.instCategoryPairCategory (stageSystem D l hl Ω Y)

noncomputable def StageHom (A B : Pair D l hl Ω Y) (L : Common A B) :=
  ((stageTransition D l hl Ω Y A.stage L.val L.property.1).obj A.obj ⟶
    (stageTransition D l hl Ω Y B.stage L.val L.property.2).obj B.obj)

@[instance_reducible]
noncomputable instance stageHomAddCommGroup (A B : Pair D l hl Ω Y) (L : Common A B) :
    AddCommGroup (StageHom A B L) :=
  (stagePreadditive D l hl Ω Y L.val).homGroup _ _

noncomputable def transport (A B : Pair D l hl Ω Y) (L M : Common A B) (h : L ≤ M)
    (f : StageHom A B L) : StageHom A B M :=
  (stageSystem D l hl Ω Y).tr h f

noncomputable def transportHom (A B : Pair D l hl Ω Y) (L M : Common A B) (h : L ≤ M) :
    StageHom A B L →+ StageHom A B M where
  toFun := transport A B L M h
  map_zero' := (transport_additive A B L M h).1
  map_add' := (transport_additive A B L M h).2

noncomputable def ColimitHom (A B : Pair D l hl Ω Y) :=
  AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)

noncomputable instance colimitHomGroup (A B : Pair D l hl Ω Y) :
    AddCommGroup (ColimitHom A B) :=
  AddCommGroup.DirectLimit.addCommGroup (StageHom A B) (transportHom A B)

noncomputable instance homAddCommGroup (A B : Pair D l hl Ω Y) : AddCommGroup (A ⟶ B) :=
  (homCoordinates A B).addCommGroup

noncomputable instance preadditive : Preadditive (Pair D l hl Ω Y) where
  homGroup A B := homAddCommGroup A B
  add_comp A B C f f' g := composition_bilinear.1 A B C f f' g
  comp_add A B C f g g' := composition_bilinear.2 A B C f g g'

noncomputable instance hasShift : HasShift (Pair D l hl Ω Y) ℤ :=
  StageSystem.PairCategory.hasShift (stageSystem D l hl Ω Y) ℤ

noncomputable instance shiftAdditive (n : ℤ) :
    (shiftFunctor (Pair D l hl Ω Y) n).Additive := by
  have h : @Functor.Additive _ _ _ _
      (StageSystem.PairCategory.preadditive (S := stageSystem D l hl Ω Y))
      (StageSystem.PairCategory.preadditive (S := stageSystem D l hl Ω Y))
      (shiftFunctor (Pair D l hl Ω Y) n) := by
    let : Preadditive (Pair D l hl Ω Y) :=
      StageSystem.PairCategory.preadditive (S := stageSystem D l hl Ω Y)
    change ((stageSystem D l hl Ω Y).shiftMorphism ℤ n).functor.Additive
    infer_instance
  exact additive_transport _ _ _ _ preadditive_eq_native preadditive_eq_native _ h

noncomputable instance inclusionCommShift (E : Index l Ω) :
    (inclusion E : Stage D l hl Ω Y E ⥤ _).CommShift ℤ :=
  StageSystem.ι_commShift E
```

The public comparison declarations `correctedTensorAssociator_formula`,
`associator_formula`, `stageSystem_transition`, `stageSystem_associator` and
`homCoordinatesAddEquiv` certify the specified data. The group and preadditive
comparison lemmas are private and fully proved.

`WeilConjectures.CategoryTheory.StageSystem.Shift` is a public import because the
public shift definitions use its data. `StageSystem.Preadditive` and
`Mathlib.Algebra.Group.Ext` are private proof imports. No original import is removed.

## Users

The table is the union of the whole-word textual matches reported by
`tools/downstream.py --uses` for the changed names. It intentionally includes matches
in independent General/Sf namespaces and generic uses of names such as `associator`.
No downstream module is adapted. An ordered `lcompile.py --all` build checked the
final overlay together with all five direct importers and the transitive General
interface: all eight files compiled with exit code zero and no warnings. The
unchanged validation sources are not included in the delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedForgetTensorTransposition | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Compactification.NagataDensityNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafFoldScalar | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdicFiniteRealizationCocone | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdicLisseCalculusData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdmissibleCupCoefficientPassages | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdmissibleHomSubstitution | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AffineCoordinateSupportStalkContinuity | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.AlgebraicallyClosedCoefficients | T3 | This delivery: proofs and certified definition changes below. |
| Sheaf.Paper.AutomorphismConstructibleStageEquivalence | B5 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ClassicalRawLisseCommonRealization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ClassicalRawLisseCommonSystem | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ClopenCommonCompactSupport | K3 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ClosedTestChainMateData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ClosedTestChainMateRestriction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CoefDualizingClosedChart | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CoefficientDualModelTransport | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CoefficientEvaluationNaturality | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CoefficientTensorNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CoefficientTwistsDetailed | R2 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CoherentRationalPullbackIdentity | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CommonStageFiniteHomLifting | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CommonStageFiniteObjectLifting | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CommonStageInclusionTensorComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CommonStageOpenHeartAdjunction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CommonStagePointReturn | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CommonStagePullbackIdentity | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CommonStageRestrictionTensorDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CommonStageWeilIterate | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CommonTransitionCoefficientMates | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompactSupportCondensedRealization | Y2 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompactSupportNormalizedScalarDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompactSupportRationalScalarIso | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompactSupportSystemTransposeNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompactSupportTowerReduction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompleteCompactificationLimitSupport | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompletedCoefficientMonoidalAdjunctionTransport | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompletedCoefficientTransportExpressions | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompletedPullbackTensorComparison | G3 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CondensedCompactSupportProjection | V9 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConstantCoefficientObjectsConstructible | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConstantExtensionSheetHeartData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientAssemblyData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConstructibleExceptionalCompositorData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConstructibleExceptionalRefinementMate | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConstructibleLeftCompositorCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConstructiblePullbackTExact | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConstructibleStandardTStructure | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ConstructibleTruncations | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CoordinateLineAdjunctionMaps | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.DerivedDirectImageOpenCoherenceData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.DerivedHomSubstitutionCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.DerivedPullbackTensorHom | T4 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.DerivedPullbackTensorIso | C7 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.DiagonalDerivedReductionExists | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.DiagonalReductionCompletion | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.DualBaseChange | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.EquivariantMatesCoefficientTransport | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.EtaleBrownGeometricComparisons | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.EtaleBrownLevelComparisons | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | B8 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.EtaleCtfChartDomain | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.EtaleProEtaleScalarPullbackCube | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.EtaleSystemBrownConstruction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.EtaleSystemCofinalData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.EtaleSystemProjectionData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.EtaleSystemScalarMateCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.EtaleTowerBrownAdjunction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ExceptionalAdjointAdmissibility | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ExceptionalCommonStageDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ExceptionalFieldDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ExceptionalFiniteRestrictionAdjunction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ExceptionalSystemInterfaces | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ExceptionalSystemTransport | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FdCoefficientComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FdCommonStageComparisonDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FdCompletionInverseScalarCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FdHomLinearEquivalence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FdIntegralInverseScalarCocycle | M3 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FdRawLocalizationScalarCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FdRawLocalizationScalarData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FdScalarRoosComparisonIntertwining | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FdShiftTriangleReflection | M8 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FieldCohomologyPerfectDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FieldShriekCompositionQcqs | C4 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | M3 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteCoefficientPoint | A9 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteCompactSupportScalarTransport | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteCounitRestrictionTowers | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteFreeCompactComposition | P8 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteKernelConstructibleLocalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteLevelProjectionFactors | M4 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteLocalizingSmoothLocalFormula | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteModelTopologyComparisonMaps | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteProductFieldCoefficientDescent | N2 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteProperLocalizing | Y6 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteProperProductTranspose | S9 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FinitePullbackTensorComparison | U5 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteRestrictionCoefficientCore | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteRestrictionCoefficientDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteRestrictionCoefficientDescentData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteRestrictionCoefficientFiniteData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteRestrictionCoefficientGeometry | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteRestrictionCoefficientNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteRestrictionDiagramModels | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteRestrictionGeometricArrows | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteRestrictionIntegralAssembly | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteRestrictionRationalAssembly | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteSitePerfectEvaluation | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteSiteWordRefinement | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FiniteTensorSignedReduction | J2 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FrobeniusPullbackOrdinaryExchange | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.FrobeniusSquareExchange | V4 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | F7 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.GeometricCommonStageDirectImage | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.GeometricOperations | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralCoherenceData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | C6 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralComparisonSequenceScalarPullbackShifts | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralDirectImageTowerData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralLineReductionDefinitions | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralQuotientPullbackFaceModel | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralSectionsPerfectReduction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralTwistAmbientCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IntrinsicQbarCategory | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IsomorphismFieldTransport | A6 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.IsomorphismPullbackTExactCoefficients | S5 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.LevelwiseNormalizedStrictSystems | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.LocalFrobeniusLargeCoefficients | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.LocallyClosedScalarPasting | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.MateOpenRestrictionMaps | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.MixedCupCoefficientChange | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.MixedCupCoefficientData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.MixedCupCoefficientSquare | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.MixedCupFieldCoordinates | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.MixedCupFieldNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.MixedCupNormalizedScalars | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.MixedCupOperationComparisons | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.MixedCupTensorClosure | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.MixedCupTensorComparisons | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.MixedCupTensorElementary | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.MixedCupTensorNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.NativeEncodingDerivedOperations | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.NativeIntegralTateTowerLimit | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.NativeScalarRestrictionComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.NativeWeilClosedModels | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.NativeWeilInductionComparisonData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.NormalizedCommonCoefficientLaws | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.NormalizedInternalSupportScalars | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.NormalizedTensorConstraintTransport | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.OpenExceptionalScalarLocality | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.OpenProEtaleCounitScalar | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.OpenScalarSiteCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.OpenSquareSupportScalarCounit | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.OperationCoefficientActionData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.OrientedDoubleHomCancellation | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.OrientedPerfectDuality | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PerfectDualPairAndTateStability | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PodCompletionReindexModels | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PodReconstructionCommonStageCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PodReindexingCompletedEvaluationReflection | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PodReindexingHomCoefficientDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PodReindexingRoosShiftCompatibility | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PointCompositeComparisonTower | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PointEquivariantDiagramData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PointFibreDerivedTensorQbar | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PointFibreEquivalence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PointHeartFiniteStageData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PointQbarFibreShiftDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PointRationalFamilyCommonStageNaturality | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PointRealizationStandardCohomology | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PointRestrictionWholeRoosSquare | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PointSectionsReconstruction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PointSystemInsertionComposition | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PointTransformationCoefficientDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PointWeilFiniteStageDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PointWeilPairingCoordinates | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PrimitiveQuotientRealizationComparisons | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ProjectionFormulaCoherence | V5 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ProjectionTensorCoefficientCocycles | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ProjectionWeilTensorDomainBridge | R3 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ProperCoefficientDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ProperEtaleOriginScalarData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ProperOpenCoefficientMate | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ProperSupportCoefficientAdjunction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PurFrameworkPbcCoefficientCategoryComparison | M4 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PurStrictIntegralExchangeNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.PuritySourceTransports | E2 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.QcqsIntegralScalarExtensionCTF | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.QuotientSystemMixedCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | B4 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.RationalRestrictionComparisonCoherence | C3 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.RealizedPullbackComparisons | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.RelativeProductFactors | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.RestrictionLocal | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ScalarCompositeMateAdjunct | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ScalarPullbackIsoExistence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ScalarPullbackIsoUniqueness | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SemilinearExchangeCubeData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SequenceScalarGeneratorInterchange | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfAdicCommonStageDescentEquivalence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfAlgebraicallyClosedCoefficients | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfCoefficientCoherentInverse | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfCommonStageFullFaithfulness | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfConstructibleHeart | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfExceptionalReductionTransitions | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfFrameworkCommonStageDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfFrameworkThetaShiftCompatibility | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfNormalizedCommonStageDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfNormalizedRecollementScalarCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfOpenClosedTriangleData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfPackageCommonStageTransport | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | F2 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfPackageQbarAdjunctionMapDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfQbarLocalizationCommonStage | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfQbarLocalizationExactDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfQbarLocalizationFiniteData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfQbarLocalizationShiftDescent | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfStrictDirectImageRationalComparisons | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfStrictDirectImageRationalData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfStrictDirectImageScalarComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfStrictDirectImageScalarData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SfWeilSheafComplex | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SitePerfectComplex | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SmoothPurityStrictPlusEvaluationRealization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SmoothPurityTowerGluingData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SupportedCommonFieldScalarData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SupportedCupFunctoriality | Q8 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SystemCompactSupportRestrictionData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SystemCompatibleCompositorNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | H9 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.TensorHomExchange | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.TowerP1SingleLevelData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.TowerReductionShiftCompatibility | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.UnboundedCoefficientPullbackModel | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.VerdierCompositionMateNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.VerdierExchange | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.VerdierHomChainComposition | Q6 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ZlImmersionWeilLocalData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ZlOpenCompactSupportRestriction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ZlOpenExtensionTExact | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ZlSfPbcNormalizedHeartModel | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SecSmoothPurity.IntrinsicCtfRefinementComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | R4 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | S1 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.AugmentedStrictIntegralCompletion | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | C4 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.CompositionProjectionData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.DetSfCompBaseChangeDefs | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.DiagramPullbackMonoidalShiftModels | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.DualizingOpenMate | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.EtaleHomComparisonModels | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.FiniteDualizingData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | H1 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.GeneratorReductionData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.IntegralCompactificationRealizationData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.IntegralOpenReductionDefinitions | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.IntegralSystemCompositorAssociativity | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.OpenProjectionRestrictionNormalization | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.ProEtale.InternalFirstResidueReductionComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | J3 | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.SemilinearOpenExternalCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.TensorAdjunctionReductionSquares | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.TensorExchangeCoherentConclusions | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.TensorExchangePresentation | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.SixFunctors.VerdierExchangeData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.TraceFormula.CounitRealizationSubstitution | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.WeilSheaf.NativeOpenProperForgetting | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.WeilSheaf.NativeOpenProperInterchange | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.AdicSystem | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralExceptionalAdjoint | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberAlgClosed | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ForgetLowerStar | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafStageMap | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarScalar | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeAdic | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.UpperStarCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TraceScalarExtension | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionCoherence | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FieldCoefficientForget | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FieldCoefficientKaroubian | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FieldCoefficientTriangulated | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FieldCoefficientTwoColimit | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FourierBaseLinear | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FourierFirstFormula | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FourierInversion.KernelComposition | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FourierInversion.Reflection | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisseComm | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FourierStalkFibre | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerShriek | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.ShiftedSheaf | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil | unclaimed | No signature edit. Exact tensor formulas and the colimit additive equivalence preserve the legacy data; other namespaces are unaffected. |

## Status

landed 20261026T002808-L-116338 2026-10-26 (merge of deliver/T3/Sheaf.Paper.AlgebraicallyClosedCoefficients)
