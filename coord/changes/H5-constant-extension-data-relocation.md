# Constant-extension data relocation

## Reason

The existing geometry proof step imports the item through ConstantExtensionSheetHeartData.
Proving constantExtensionCyclicSheets from this stated step would therefore introduce an
import cycle. Extract the existing data and already complete geometric compatibility proofs
to ConstantExtensionWeilHeartData, and publicly reexport them from the item. No mathematical
definition, existing declaration signature, public visibility or target statement changes.
This is an import-cycle repair, not a compile-time split.

## Old

ConstantExtensionWeilHeartEquivalence contained the 31 data/compatibility declarations listed
by its old DAG attachment, plus the two remaining theorem holes. It publicly imported
Sheaf.Paper.AdicPunctualWeights and Sheaf.AlgebraicGeometry.FrobeniusDetailed.
ConstantExtensionSheetHeartData began with:

```lean
public import Sheaf.Paper.ConstantExtensionWeilHeartEquivalence
```

## New

All 31 data/compatibility declarations, with their original signatures, attributes,
docstrings and bodies verbatim, are in ConstantExtensionWeilHeartData. Its public imports
are the two old public imports verbatim. The item publicly imports that data module;
ConstantExtensionSheetHeartData replaces the import above with:

```lean
public import Sheaf.Paper.ConstantExtensionWeilHeartData
```

The item proves constantExtensionCyclicSheets from constantExtensionSheetGeometry. It keeps
constantExtensionWeilHeartEquivalence unchanged with its existing sorry. The relocation
preserves every existing object exactly; it does not change the meaning of any target.
A declaration-table comparison confirms unchanged statements and bodies except for the
filled cyclic-sheet proof. Existing definition-owner DAG records point to the data module.

The following declaration signatures are identical in the old and new location
(normalized whitespace; the declaration bodies are copied byte for byte):

```lean
theorem constantExtensionField_properties : Finite (D.extensionSubfield m hm) ∧ Nat.card
  (D.extensionSubfield m hm) = D.q ^ m ∧ IsAlgClosure (D.extensionSubfield m hm) D.k

def constantExtensionDatum : FiniteFieldDatum.{u}

def constantExtensionModel : Over (Spec (.of (D.extensionSubfield m hm)))

def constantExtensionOriginalModel : Over (Spec (.of D.k₀))

theorem constantExtensionModel_properties : LocallyOfFiniteType (constantExtensionModel D m hm
  X₀).hom ∧ QuasiCompact (constantExtensionModel D m hm X₀).hom ∧ LocallyOfFiniteType
  (constantExtensionOriginalModel D m hm X₀).hom ∧ QuasiCompact (constantExtensionOriginalModel D
  m hm X₀).hom

instance constantExtensionModel_lft : LocallyOfFiniteType (constantExtensionModel D m hm X₀).hom

instance constantExtensionModel_qc : QuasiCompact (constantExtensionModel D m hm X₀).hom

instance constantExtensionOriginalModel_lft : LocallyOfFiniteType (constantExtensionOriginalModel
  D m hm X₀).hom

instance constantExtensionOriginalModel_qc : QuasiCompact (constantExtensionOriginalModel D m hm
  X₀).hom

def constantExtensionProjection : constantExtensionOriginalModel D m hm X₀ ⟶ X₀

theorem constantExtensionSheet_compatible : pullback.fst (constantExtensionModel D m hm X₀).hom
  (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) ≫
  (constantExtensionOriginalModel D m hm X₀).hom = ((constantExtensionDatum D m hm).geometricFiber
  (constantExtensionModel D m hm X₀)).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))

def constantExtensionSheet : ((constantExtensionDatum D m hm).geometricFiber
  (constantExtensionModel D m hm X₀)).left ⟶ (D.geometricFiber (constantExtensionOriginalModel D m
  hm X₀)).left

theorem constantExtensionFiberMap_isIso : IsIso (constantExtensionSheet D m hm X₀ ≫ zlFiberMap D
  (constantExtensionProjection D m hm X₀))

def constantExtensionFiberIso : ((constantExtensionDatum D m hm).geometricFiber
  (constantExtensionModel D m hm X₀)).left ≅ (D.geometricFiber X₀).left

theorem constantExtensionSheet_return : ((constantExtensionDatum D m hm).geometricFrobenius
  (constantExtensionModel D m hm X₀)).hom ≫ constantExtensionSheet D m hm X₀ =
  constantExtensionSheet D m hm X₀ ≫ localPositivePower (D.geometricFrobenius
  (constantExtensionOriginalModel D m hm X₀)).hom (m - 1)

def constantExtensionSheetPull

def constantExtensionWeilIterate (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
  [QuasiCompact Y₀.hom] (K : sfCommonStageWeilComplex D l hl Y₀ Ω) : (n : ℕ) →
  (@commonStageDerivedPullback l _ Ω _ _ _ _ _ (localPositivePower (D.geometricFrobenius Y₀).hom
  n) (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj K.carrier ≅
  K.carrier

def constantExtensionReturnComparison (M : generalAlgebraicallyClosedConstructibleCategory l Ω
  (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left) :
  (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl (constantExtensionModel
  D m hm X₀) Ω).obj ((constantExtensionSheetPull D m hm X₀ l hl Ω).obj M) ≅
  (constantExtensionSheetPull D m hm X₀ l hl Ω).obj ((@commonStageDerivedPullback l _ Ω _ _ _ _ _
  (localPositivePower (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom (m -
  1)) (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))
  (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀))).obj M)

def constantExtensionHeartForget (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
  [QuasiCompact Y₀.hom]

def ConstantExtensionSheetSpec (T : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel
  D m hm X₀) Ω ⥤ sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
  (constantExtensionModel D m hm X₀) Ω) : Prop

def constantExtensionResidueDegree (z : (constantExtensionModel D m hm X₀).left) : ℕ

theorem constantExtensionClosedImage_mem (z : {z : (constantExtensionModel D m hm X₀).left // z ∈
  closedPoints (constantExtensionModel D m hm X₀).left}) : (constantExtensionProjection D m hm
  X₀).left z.val ∈ closedPoints X₀.left

def constantExtensionClosedImage (z : {z : (constantExtensionModel D m hm X₀).left // z ∈
  closedPoints (constantExtensionModel D m hm X₀).left}) : {x : X₀.left // x ∈ closedPoints
  X₀.left}

def ConstantExtensionLocalConjugacy (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
  [QuasiCompact Y₀.hom] (F : sfCommonStageWeilSheaf D l hl Y₀ Ω) (G : sfCommonStageWeilSheaf
  (constantExtensionDatum D m hm) l hl (constantExtensionModel D m hm X₀) Ω) (x : {x : Y₀.left //
  x ∈ closedPoints Y₀.left}) (z : {z : (constantExtensionModel D m hm X₀).left // z ∈ closedPoints
  (constantExtensionModel D m hm X₀).left}) (f : ℕ) : Prop

def constantExtensionCyclicSheet (i : Fin m) : (D.geometricFiber X₀).left ⟶ (D.geometricFiber
  (constantExtensionOriginalModel D m hm X₀)).left

def constantExtensionRestriction (e : sfCommonStageWeilSheaf D l hl
  (constantExtensionOriginalModel D m hm X₀) Ω ≌ sfCommonStageWeilSheaf (constantExtensionDatum D
  m hm) l hl (constantExtensionModel D m hm X₀) Ω)

theorem constantExtensionFiber_return : ((constantExtensionDatum D m hm).geometricFrobenius
  (constantExtensionModel D m hm X₀)).hom ≫ (constantExtensionFiberIso D m hm X₀).hom =
  (constantExtensionFiberIso D m hm X₀).hom ≫ localPositivePower (D.geometricFrobenius X₀).hom (m
  - 1)

def constantExtensionFiberPull

def constantExtensionRestrictionComparison (M : generalAlgebraicallyClosedConstructibleCategory l
  Ω (D.geometricFiber X₀).left) : (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m
  hm) l hl (constantExtensionModel D m hm X₀) Ω).obj ((constantExtensionFiberPull D m hm X₀ l hl
  Ω).obj M) ≅ (constantExtensionFiberPull D m hm X₀ l hl Ω).obj ((@commonStageDerivedPullback l _
  Ω _ _ _ _ _ (localPositivePower (D.geometricFrobenius X₀).hom (m - 1)) (sfWeilPrimeInvertible D
  l hl X₀) (sfWeilPrimeInvertible D l hl X₀)).obj M)

def ConstantExtensionRestrictionSpec (R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
  sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl (constantExtensionModel D m hm X₀)
  Ω) : Prop

def constantExtensionSheetPullAt (i : Fin m)

```

## Users

The prescribed tools/downstream.py scan lists the following transitive users. All retain
the same public declarations and transitive public imports through the data reexport.
Only ConstantExtensionSheetHeartData needs an import adaptation. It is unclaimed in the
current local claim snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | H5 | Proof of cyclic sheets; same public signatures and reexports. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ClassicalFrontierExistence | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | D6 | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnData | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnExactFunctor | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalSpectra | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnTransportComparison | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetGeometry | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartData | unclaimed | Replace parent import by extracted data import to prevent the cycle; all declarations unchanged. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | T1 | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Identical public names, signatures and definition bodies; no adaptation. |

## Status

landed 20261025T202206-L-2690002 2026-10-25 (merge of deliver/H5/Sheaf.Paper.ConstantExtensionWeilHeartEquivalence)
