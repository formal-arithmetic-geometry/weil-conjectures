# Scalar balancing coefficient data attachments

## Reason

The first delivery preflight refused both new proof dependencies because the old
coarse native/support and constant-scalar/mate nodes reach back to the balancing
item through compact-support comparison. Separate their existing coefficient-only
declaration attachments from their later geometric conclusions. No existing Lean
file, declaration, body, attribute, visibility or import changes. No mathematical
statement changes. The auxiliary proof dependencies name these smaller data nodes.

## Old
### def-pur-constant-scalar-tower-adjunction

```json
{
 "stmt_deps": [
  "def-weil-l-adic-coefficient-extension",
  "def-cbc-strict-constant-tower-operations",
  "lem-pur-derived-change-of-rings",
  "def-pc-sheaf-restrict-scalars",
  "def-pur-integral-compact-support-coefficient-data"
 ],
 "lean": {
  "module": "Sheaf.Paper.ConstantScalarTowerAdjunction",
  "declaration": "WeilConjectures.PurStrictScalar.scalarAdj",
  "declarations": [
   "WeilConjectures.PurStrictScalar.constantMap",
   "WeilConjectures.PurStrictScalar.tensor",
   "WeilConjectures.PurStrictScalar.restrict",
   "WeilConjectures.PurStrictScalar.tensor_exact",
   "WeilConjectures.PurStrictScalar.T",
   "WeilConjectures.PurStrictScalar.restrict_limits",
   "WeilConjectures.PurStrictScalar.restrict_colimits",
   "WeilConjectures.PurStrictScalar.U",
   "WeilConjectures.PurStrictScalar.scalarAdj",
   "WeilConjectures.PurStrictScalar.constants",
   "WeilConjectures.PurStrictScalar.change"
  ],
  "file": "lean/Sheaf/Paper/ConstantScalarTowerAdjunction.lean",
  "statement": "def scalarAdj (W : Scheme.{u}) : T l E F i W ⊣ U l E F i W",
  "branch": "newtargets-dag",
  "by": "N6",
  "date": "2026-10-23",
  "existing": false
 }
}
```
### def-pur-constant-scalar-tower-mates

```json
{
 "stmt_deps": [
  "def-weil-l-adic-coefficient-extension",
  "def-cbc-strict-constant-tower-operations",
  "def-cbc-strict-tower-open-extension",
  "def-pc-sheaf-restrict-scalars",
  "lem-pur-derived-change-of-rings",
  "def-pur-integral-compact-support-coefficient-data",
  "def-weil-compactifications-refinements",
  "def-pur-constant-scalar-tower-adjunction"
 ],
 "lean": {
  "module": "Sheaf.Paper.ConstantScalarTowerMates",
  "declaration": "WeilConjectures.PurStrictScalar.comparison",
  "declarations": [
   "WeilConjectures.PurStrictScalar.derivedUnit",
   "WeilConjectures.PurStrictScalar.unitCompatible",
   "WeilConjectures.PurStrictScalar.properRestrictionOrdinary_existsUnique",
   "WeilConjectures.PurStrictScalar.properRestrictionOrdinary",
   "WeilConjectures.PurStrictScalar.properRestriction_existsUnique",
   "WeilConjectures.PurStrictScalar.properRestriction",
   "WeilConjectures.PurStrictScalar.proper",
   "WeilConjectures.PurStrictScalar.openRestrictionOrdinary",
   "WeilConjectures.PurStrictScalar.openRestriction",
   "WeilConjectures.PurStrictScalar.openTensor",
   "WeilConjectures.PurStrictScalar.image",
   "WeilConjectures.PurStrictScalar.comparison"
  ],
  "file": "lean/Sheaf/Paper/ConstantScalarTowerMates.lean",
  "statement": "def comparison {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : image l E c ⋙ T l E F i Y ⟶ T l E F i X ⋙ image l F c",
  "branch": "newtargets-dag",
  "by": "N6",
  "date": "2026-10-23",
  "existing": false
 }
}
```
### def-pur-native-constant-support-model

```json
{
 "stmt_deps": [
  "def-pur-constant-scalar-tower-mates",
  "lem-weil-compact-support-reduction-tower-functor",
  "def-coef-derived-system-calculus-data",
  "def-weil-completed-integral-coefficients",
  "lem-pur-system-ringed-sequence-site",
  "def-weil-compact-support-native-system-evaluation"
 ],
 "lean": {
  "module": "Sheaf.Paper.NativeConstantSupportModel",
  "declaration": "WeilConjectures.PurStrictScalar.support",
  "declarations": [
   "WeilConjectures.PurStrictScalar.constantRestriction",
   "WeilConjectures.PurStrictScalar.towerConstantRestriction",
   "WeilConjectures.PurStrictScalar.towerConstantRestriction_exact",
   "WeilConjectures.PurStrictScalar.toConstant",
   "WeilConjectures.PurStrictScalar.systemRestriction",
   "WeilConjectures.PurStrictScalar.systemRestriction_exact",
   "WeilConjectures.PurStrictScalar.systemRestriction_limits",
   "WeilConjectures.PurStrictScalar.systemRestriction_colimits",
   "WeilConjectures.PurStrictScalar.systemRestriction_additive",
   "WeilConjectures.PurStrictScalar.pushRestriction_zero",
   "WeilConjectures.PurStrictScalar.restrictionPush_zero",
   "WeilConjectures.PurStrictScalar.systemU",
   "WeilConjectures.PurStrictScalar.systemProperOrdinary_existsUnique",
   "WeilConjectures.PurStrictScalar.systemProperOrdinary",
   "WeilConjectures.PurStrictScalar.nativePush_additive",
   "WeilConjectures.PurStrictScalar.systemProper_existsUnique",
   "WeilConjectures.PurStrictScalar.systemProper",
   "WeilConjectures.PurStrictScalar.systemPullMap",
   "WeilConjectures.PurStrictScalar.systemPullMap_isIso",
   "WeilConjectures.PurStrictScalar.systemOpenMap",
   "WeilConjectures.PurStrictScalar.systemOpenMap_isIso",
   "WeilConjectures.PurStrictScalar.systemOpen",
   "WeilConjectures.PurStrictScalar.reduction",
   "WeilConjectures.PurStrictScalar.ordinaryLimit",
   "WeilConjectures.PurStrictScalar.ordinaryLimit_rightAdjoint",
   "WeilConjectures.PurStrictScalar.ordinaryLimit_isRightAdjoint",
   "WeilConjectures.PurStrictScalar.ordinaryReduction",
   "WeilConjectures.PurStrictScalar.ordinaryReductionAdj",
   "WeilConjectures.PurStrictScalar.ordinaryReduction_additive_data",
   "WeilConjectures.PurStrictScalar.ordinaryLimit_additive",
   "WeilConjectures.PurStrictScalar.ordinaryReduction_additive",
   "WeilConjectures.PurStrictScalar.reductionRightComparison_existsUnique",
   "WeilConjectures.PurStrictScalar.reductionRightComparison",
   "WeilConjectures.PurStrictScalar.systemReductionCounit",
   "WeilConjectures.PurStrictScalar.support",
   "WeilConjectures.PurStrictScalar.supportModel",
   "WeilConjectures.PurStrictScalar.nativeSequence_kInjective"
  ],
  "file": "lean/Sheaf/Paper/NativeConstantSupportModel.lean",
  "statement": "def support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (S : CoefficientDerivedSystemCalculus.{u, u} l E X)",
  "branch": "newtargets-dag",
  "by": "N6",
  "date": "2026-10-23",
  "existing": false
 }
}
```

## New

Partition the existing declaration lists as follows; each declaration remains
attached exactly once across its old record and the new record. The main
attachment of each old node remains unchanged. Their statements and proof routes
are unchanged. Each old node adds its extracted data node as a statement
dependency. No module is relocated or redeclared.

### def-pur-constant-scalar-tensor-data

```json
{
 "existing": true,
 "module": "Sheaf.Paper.ConstantScalarTowerAdjunction",
 "file": "lean/Sheaf/Paper/ConstantScalarTowerAdjunction.lean",
 "declaration": "WeilConjectures.PurStrictScalar.T",
 "declarations": [
  "WeilConjectures.PurStrictScalar.constantMap",
  "WeilConjectures.PurStrictScalar.tensor",
  "WeilConjectures.PurStrictScalar.tensor_exact",
  "WeilConjectures.PurStrictScalar.T",
  "WeilConjectures.PurStrictScalar.constants"
 ],
 "statement": "def T (W : Scheme.{u}) :\n    Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤\n      Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W",
 "branch": "sheaf-dag",
 "by": "C3",
 "date": "2026-10-25",
 "note": "Existing coefficient-only declarations reattached from def-pur-constant-scalar-tower-adjunction without any Lean change; the old node retains geometric/support declarations."
}
```

### def-pur-whole-cochain-derived-unit

```json
{
 "existing": true,
 "module": "Sheaf.Paper.ConstantScalarTowerMates",
 "file": "lean/Sheaf/Paper/ConstantScalarTowerMates.lean",
 "declaration": "WeilConjectures.PurStrictScalar.derivedUnit",
 "declarations": [
  "WeilConjectures.PurStrictScalar.derivedUnit"
 ],
 "statement": "def derivedUnit {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]\n    [Abelian A] [Abelian B]\n    [HasDerivedCategory.{wa} A] [HasDerivedCategory.{wb} B]\n    [Abelian.HasKInjectiveResolutions A]\n    (H : A ⥤ B) [H.Additive] (K : CochainComplex A ℤ) :\n    DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj K) ⟶\n      H.rightDerivedFunctor.obj (DerivedCategory.Q.obj K)",
 "branch": "sheaf-dag",
 "by": "C3",
 "date": "2026-10-25",
 "note": "Existing coefficient-only declarations reattached from def-pur-constant-scalar-tower-mates without any Lean change; the old node retains geometric/support declarations."
}
```

### def-pur-native-reduction-counit-data

```json
{
 "existing": true,
 "module": "Sheaf.Paper.NativeConstantSupportModel",
 "file": "lean/Sheaf/Paper/NativeConstantSupportModel.lean",
 "declaration": "WeilConjectures.PurStrictScalar.systemReductionCounit",
 "declarations": [
  "WeilConjectures.PurStrictScalar.constantRestriction",
  "WeilConjectures.PurStrictScalar.towerConstantRestriction",
  "WeilConjectures.PurStrictScalar.towerConstantRestriction_exact",
  "WeilConjectures.PurStrictScalar.toConstant",
  "WeilConjectures.PurStrictScalar.systemRestriction",
  "WeilConjectures.PurStrictScalar.systemRestriction_exact",
  "WeilConjectures.PurStrictScalar.systemRestriction_limits",
  "WeilConjectures.PurStrictScalar.systemRestriction_colimits",
  "WeilConjectures.PurStrictScalar.systemRestriction_additive",
  "WeilConjectures.PurStrictScalar.systemU",
  "WeilConjectures.PurStrictScalar.reduction",
  "WeilConjectures.PurStrictScalar.ordinaryLimit",
  "WeilConjectures.PurStrictScalar.ordinaryLimit_rightAdjoint",
  "WeilConjectures.PurStrictScalar.ordinaryLimit_isRightAdjoint",
  "WeilConjectures.PurStrictScalar.ordinaryReduction",
  "WeilConjectures.PurStrictScalar.ordinaryReductionAdj",
  "WeilConjectures.PurStrictScalar.ordinaryReduction_additive_data",
  "WeilConjectures.PurStrictScalar.ordinaryLimit_additive",
  "WeilConjectures.PurStrictScalar.ordinaryReduction_additive",
  "WeilConjectures.PurStrictScalar.reductionRightComparison_existsUnique",
  "WeilConjectures.PurStrictScalar.reductionRightComparison",
  "WeilConjectures.PurStrictScalar.systemReductionCounit"
 ],
 "statement": "def systemReductionCounit (W : Scheme.{u})\n    (S : CoefficientDerivedSystemCalculus.{u, u} l E W) :\n    DerivedCategory.Qh ⋙ S.reduction ⟶\n      (ordinaryReduction l E W).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh",
 "branch": "sheaf-dag",
 "by": "C3",
 "date": "2026-10-25",
 "note": "Existing coefficient-only declarations reattached from def-pur-native-constant-support-model without any Lean change; the old node retains geometric/support declarations."
}
```

## Users

The downstream.py checks covered each original module and the representative
names T, derivedUnit and systemReductionCounit. All existing signatures, objects
and mathematical meanings are identical; only DAG ownership becomes finer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportCoefficientModels | R7 | No existing Lean change or adaptation; attachment precision only. |
| Sheaf.Paper.CompactSupportCompletedScalarArrow | unclaimed | No existing Lean change or adaptation; attachment precision only. |
| Sheaf.Paper.CompactSupportScalarLimitReduction | E2 | No existing Lean change or adaptation; attachment precision only. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | U6 | No existing Lean change or adaptation; attachment precision only. |
| Sheaf.Paper.CompactSupportScalarShiftNormalization | Q2 | No existing Lean change or adaptation; attachment precision only. |
| Sheaf.Paper.CompactSupportStrictScalarComposition | S3 | No existing Lean change or adaptation; attachment precision only. |
| Sheaf.Paper.CompactSupportStrictScalarMate | P5 | No existing Lean change or adaptation; attachment precision only. |
| Sheaf.Paper.CompactSupportStrictScalarRefinement | G3 | No existing Lean change or adaptation; attachment precision only. |
| Sheaf.Paper.ConstantScalarTowerAdjunction | A9 | No existing Lean change or adaptation; attachment precision only. |
| Sheaf.Paper.ConstantScalarTowerMates | B6 | No existing Lean change or adaptation; attachment precision only. |
| Sheaf.Paper.NativeConstantSupportModel | X6 | No existing Lean change or adaptation; attachment precision only. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | V6 | No existing Lean change or adaptation; attachment precision only. |
| Sheaf.Paper.ScalarReductionTowerBalancing | C3 | No existing Lean change or adaptation; attachment precision only. |
| Sheaf.Paper.ScalarSourceCounitUniversal | C3 new module | Cites the extracted coefficient data nodes. |
| Sheaf.Paper.ScalarTargetCounitUniversal | C3 new module | Cites the extracted coefficient data nodes. |

The targets' statements and all definitions they use retain identical Lean text,
so no semantic target review is reopened by this metadata partition. There are
no forced adaptations, including in ConstantScalarTowerAdjunction held by A9:
its Lean source is not delivered or changed.

## Status

landed 20261025T163558-L-701181 2026-10-25 (merge of deliver/C3/Sheaf.Paper.ScalarReductionTowerBalancing)
