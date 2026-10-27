# WeilConjectures.PodRawReconstruction finite identity constructors

## Reason

Relocate finiteOpenIdentity, finiteIdentity and finiteRestrictedIdentity to the new
Sheaf.Paper.PodIdentityReductionTower module so the strict tower comparison can name
these actual constructions without importing its consumer. The original item publicly
reexports the new module. Declaration names, universes, signatures, attributes and bodies
are identical. No source-library declaration is changed. The two public theorem signatures
of the item are unchanged.

## Old

In lean/Sheaf/Paper/PodReconstructionRawRationalNaturality.lean:

```lean
/-- Identity extension by zero in the intrinsic constant-ring presentation, obtained
from the specified realization equivalence and the open-sheaf identity adjunction.
Source: blueprint opening sentence, identity compactification
(blueprint: lem-pod-reconstruction-raw-rational-naturality). -/
def finiteOpenIdentity (n : ℕ) :
    Scheme.sfIntrinsicExtensionByZero (𝟙 (point D))
      (Padic.coefficientExtensionRing l E (n + 1)) ≅ 𝟭 _ :=
  isoWhiskerLeft
      (Scheme.sfIntrinsicModuleEquivalence (point D)
        (Padic.coefficientExtensionRing l E (n + 1))).inverse
      (isoWhiskerRight
        (AlgebraicGeometry.ProEtale.openImmersionLowerShriekIdIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E (n + 1)))) (point D))
        (Scheme.sfIntrinsicModuleEquivalence (point D)
          (Padic.coefficientExtensionRing l E (n + 1))).functor ≪≫
        Functor.leftUnitor _) ≪≫
    (Scheme.sfIntrinsicModuleEquivalence (point D)
      (Padic.coefficientExtensionRing l E (n + 1))).counitIso

/-- The fixed finite-level compact-support identity: exact identity open extension,
then the K-injective-normalized identity direct image. Source: blueprint opening
sentence (blueprint: lem-pod-reconstruction-raw-rational-naturality). -/
def finiteIdentity (n : ℕ) :
    Scheme.sfIntrinsicCompactSupport (Compactification.ofIsProper (𝟙 (point D)))
      (Padic.coefficientExtensionRing l E (n + 1)) ≅ 𝟭 _ :=
  isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso (finiteOpenIdentity D l E n) ≪≫
        Functor.mapDerivedCategoryIdIso _)
      (Scheme.proEtaleConstantDerivedDirectImage (𝟙 (point D))
        (Padic.coefficientExtensionRing l E (n + 1))) ≪≫
    Functor.leftUnitor _ ≪≫
    Scheme.proEtaleGlobalEvaluationDirectImageId
      (Padic.coefficientExtensionRing l E (n + 1)) (point D)

/-- The identity finite operation applied to actual reduction and restriction.
Source: blueprint opening sentence, strict tower
(blueprint: lem-pod-reconstruction-raw-rational-naturality). -/
def finiteRestrictedIdentity (n : ℕ) :
    compactSupportRestrictedLevel l E (Compactification.ofIsProper (𝟙 (point D))) n ≅
      scalarReductionDerivedExtension l E (point D) n ⋙
        scalarReductionDerivedRestriction l E (point D) n :=
  isoWhiskerLeft (scalarReductionDerivedExtension l E (point D) n)
      (isoWhiskerRight (finiteIdentity D l E n)
        (scalarReductionDerivedRestriction l E (point D) n) ≪≫ Functor.leftUnitor _)
```

## New

The same declarations, verbatim, in lean/Sheaf/Paper/PodIdentityReductionTower.lean:

```lean
/-- Identity extension by zero in the intrinsic constant-ring presentation, obtained
from the specified realization equivalence and the open-sheaf identity adjunction.
Source: blueprint opening sentence, identity compactification
(blueprint: lem-pod-reconstruction-raw-rational-naturality). -/
def finiteOpenIdentity (n : ℕ) :
    Scheme.sfIntrinsicExtensionByZero (𝟙 (point D))
      (Padic.coefficientExtensionRing l E (n + 1)) ≅ 𝟭 _ :=
  isoWhiskerLeft
      (Scheme.sfIntrinsicModuleEquivalence (point D)
        (Padic.coefficientExtensionRing l E (n + 1))).inverse
      (isoWhiskerRight
        (AlgebraicGeometry.ProEtale.openImmersionLowerShriekIdIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u}
            (Padic.coefficientExtensionRing l E (n + 1)))) (point D))
        (Scheme.sfIntrinsicModuleEquivalence (point D)
          (Padic.coefficientExtensionRing l E (n + 1))).functor ≪≫
        Functor.leftUnitor _) ≪≫
    (Scheme.sfIntrinsicModuleEquivalence (point D)
      (Padic.coefficientExtensionRing l E (n + 1))).counitIso

/-- The fixed finite-level compact-support identity: exact identity open extension,
then the K-injective-normalized identity direct image. Source: blueprint opening
sentence (blueprint: lem-pod-reconstruction-raw-rational-naturality). -/
def finiteIdentity (n : ℕ) :
    Scheme.sfIntrinsicCompactSupport (Compactification.ofIsProper (𝟙 (point D)))
      (Padic.coefficientExtensionRing l E (n + 1)) ≅ 𝟭 _ :=
  isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso (finiteOpenIdentity D l E n) ≪≫
        Functor.mapDerivedCategoryIdIso _)
      (Scheme.proEtaleConstantDerivedDirectImage (𝟙 (point D))
        (Padic.coefficientExtensionRing l E (n + 1))) ≪≫
    Functor.leftUnitor _ ≪≫
    Scheme.proEtaleGlobalEvaluationDirectImageId
      (Padic.coefficientExtensionRing l E (n + 1)) (point D)

/-- The identity finite operation applied to actual reduction and restriction.
Source: blueprint opening sentence, strict tower
(blueprint: lem-pod-reconstruction-raw-rational-naturality). -/
def finiteRestrictedIdentity (n : ℕ) :
    compactSupportRestrictedLevel l E (Compactification.ofIsProper (𝟙 (point D))) n ≅
      scalarReductionDerivedExtension l E (point D) n ⋙
        scalarReductionDerivedRestriction l E (point D) n :=
  isoWhiskerLeft (scalarReductionDerivedExtension l E (point D) n)
      (isoWhiskerRight (finiteIdentity D l E n)
        (scalarReductionDerivedRestriction l E (point D) n) ≪≫ Functor.leftUnitor _)
```

The original module adds `public import Sheaf.Paper.PodIdentityReductionTower`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PodReconstructionRawRationalNaturality | Y8 | Public reexport preserves all names and meanings; consumes the new strict-tower theorem. |
| Sheaf.Paper.PodReconstructionCommonStageData | unclaimed in current local claims | Uses finiteRestrictedIdentity in IdentitySupport; identical declaration through the original module's public reexport, no adaptation. |
| Sheaf.Paper.PodReconstructionCommonStageCoherence | unclaimed in current local claims | Consumer of IdentitySupport; unchanged statements and proofs, no adaptation. |
| Sheaf.Paper.PodReconstructionScalarRealizations | unclaimed in current local claims | Consumer of the common-stage data; unchanged statements and proofs, no adaptation. |
| Sheaf.Paper.PodIdentityReductionTower | Y8, new | Owns the unchanged constructors and their strict-tower comparison. |
| Sheaf.Paper.CompactSupportNormalizedTowerLimit | Y8, new | Independent normalized limit theorem; no use of the moved constructors. |

`tools/downstream.py` was run for each of the three fully qualified declaration names.
Only the item uses finiteOpenIdentity and finiteIdentity; the item and common-stage
data use finiteRestrictedIdentity. IdentitySupport, the common-stage theorem, and
scalar-realization statements retain their original types and mathematical meaning. No target definition
changes.

## Status

landed 20261026T024258-L-654920 2026-10-26 (merge of deliver/Y8/Sheaf.Paper.PodReconstructionRawRationalNaturality)
