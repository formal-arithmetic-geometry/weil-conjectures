# WeilConjectures.AdicSmoothDualizing integration maps

## Reason

Restore the quarantined stage-3 item and repair the elaboration failure recorded in
coord/rework.tsv. The archived rationalIntegration timed out while inferring its
large composite type; the resulting missing declaration also broke closedIntegration.
The three integration maps now have explicit Hom result types and irreducible
attributes. Their defining composites are unchanged. The module locally treats
PurCompactSupport.image, sfIntrinsicModuleEquivalence and
ProEtale.comparisonUpperStar and finiteEtaleTateTensorFamily as irreducible, with scoped backward transparency options
at finitePowerComparison, twistReduction, IsNormalizedIntegralIntegration,
rationalIntegration and closedIntegration. These changes control elaboration;
they do not change any object, morphism, predicate, binder or normalization.
The unused public import Sheaf.Paper.CommonStageCompactWeilCohomology is removed.
Neither direct quarantined consumer refers to its cohomology declarations. The
actual compact-support maps continue to use the original coefficient-system
operations. The exactSingleShiftIso definition is also locally irreducible after its declaration.
The flatness proof uses finiteEtaleTateTensorFamily_obj explicitly, avoiding
unfolding the normalized signed-power construction. No public reducibility
attribute on these imported definitions changes. No source-library module is edited.

## Old

```lean
def integralCounitAmbient (d : ℕ)
    (e : (operation P X S (.integral (fieldStage P))).G.obj
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
      integralTwist P X (X ↘ Spec (.of P.field.k)) d) :=
  (S.ring.left (compactification P X)
      (.integral (fieldStage P))).inv.app
        (integralTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
    (finiteTorConstructibleIntegral P.coefficients.l P.extension
      (Spec (.of P.field.k))).ι.map (integralCounit P X S d e)
```

```lean
def rationalIntegration (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :=
  (S.fields.rationalizationComparison (compactification P X) (fieldStage P)).q.inv.app
      (integralTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
    (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
      (fieldStage P) (Spec (.of P.field.k))).map
        (integralCounit P X S d (integralIdentification P X S d))
```

```lean
def closedIntegration (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :=
  (S.common.commonComparison (compactification P X) (fieldIndex P)).q.inv.app
      ((modelScalar P X).obj (rationalTwist P X (X ↘ Spec (.of P.field.k)) d)) ≫
    (commonInclusion P (Spec (.of P.field.k))).map
      ((S.fields.rationalComparison (compactification P X) (fieldStage P)
          (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
            (fieldIndex P)) (modelEmbedding P)).q.inv.app
              (rationalTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
        (modelScalar P (Spec (.of P.field.k))).map (rationalIntegration P X S d))
```

## New

```lean
@[irreducible]
def integralCounitAmbient (d : ℕ)
    (e : (operation P X S (.integral (fieldStage P))).G.obj
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0) ≅
      integralTwist P X (X ↘ Spec (.of P.field.k)) d) :
    (PurCompactSupport.image
        (PurCompactSupport.completed P.coefficients.l P.extension) (compactification P X)).obj
          (integralTwist P X (X ↘ Spec (.of P.field.k)) d).obj ⟶
      (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0).obj :=
  (S.ring.left (compactification P X)
      (.integral (fieldStage P))).inv.app
        (integralTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
    (finiteTorConstructibleIntegral P.coefficients.l P.extension
      (Spec (.of P.field.k))).ι.map (integralCounit P X S d e)
```

```lean
@[irreducible]
def rationalIntegration (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S (.rational (fieldStage P))).F.obj
        (rationalTwist P X (X ↘ Spec (.of P.field.k)) d) ⟶
      rationalTwist P (Spec (.of P.field.k)) (𝟙 _) 0 :=
  (S.fields.rationalizationComparison (compactification P X) (fieldStage P)).q.inv.app
      (integralTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
    (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
      (fieldStage P) (Spec (.of P.field.k))).map
        (integralCounit P X S d (integralIdentification P X S d))
```

```lean
@[irreducible]
def closedIntegration (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))] :
    (operation P X S .closed).F.obj
        (closedTwist P X (X ↘ Spec (.of P.field.k)) d) ⟶
      closedTwist P (Spec (.of P.field.k)) (𝟙 _) 0 :=
  (S.common.commonComparison (compactification P X) (fieldIndex P)).q.inv.app
      ((modelScalar P X).obj (rationalTwist P X (X ↘ Spec (.of P.field.k)) d)) ≫
    (commonInclusion P (Spec (.of P.field.k))).map
      ((S.fields.rationalComparison (compactification P X) (fieldStage P)
          (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
            (fieldIndex P)) (modelEmbedding P)).q.inv.app
              (rationalTwist P X (X ↘ Spec (.of P.field.k)) d) ≫
        (modelScalar P (Spec (.of P.field.k))).map (rationalIntegration P X S d))
```

## Users

`tools/downstream.py Sheaf.Paper.AdicSmoothDualizingComplexes --allow-missing
--uses integralCounitAmbient rationalIntegration closedIntegration` reports zero
live downstream modules and zero external uses of all three maps. A separate
import-graph scan including `quarantine/Sheaf` finds the consumers below.
Searching both live and quarantined Lean sources finds no external reference to
these three integration definitions. Every old defining composite is HEq to the
corresponding new map: the three interface examples unfold only the named map and
close by rfl (lcompile result 65e8219e6326a68ca4339fd5, clean, 9.1 seconds).
Consequently these consumers' statement meanings are unchanged. No forced adaptation
is needed and no other group's module is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicSmoothDualizingComplexes | A2 | restored, elaboration repaired; five proofs filled |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | direct public importer; no use of modified maps |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed | direct proof importer; no use of modified maps |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | S3 | transitive importer; no statement change |
| Sheaf.Paper.RationalPurityPresentation | Q4 | transitive importer; no statement change |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | transitive importer; no statement change |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | transitive importer; no statement change |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | transitive importer; no statement change |

No semantic target statement or definition changes. The reviewer should verify
that the three annotations describe exactly the old inferred Hom types; the
interface equality checks establish that the maps themselves are unchanged.

## Status

landed 20261024T184511-L-3056387 2026-10-24 (merge of deliver/A2/Sheaf.Paper.AdicSmoothDualizingComplexes)
