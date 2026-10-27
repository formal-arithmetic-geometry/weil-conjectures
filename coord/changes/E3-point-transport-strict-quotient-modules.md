# WeilConjectures.strictQuotientPointMap

## Reason

The complete proof in one file exceeded the 60-second compile limit after replacing
broad rewriting with direct equalities and avoiding quotient substitution in finite
calculations. Move the existing model definitions to a small module, publicly
re-export it from the item, and compile the proved section, strict-identity and
finite-evaluation calculations separately. Every existing declaration keeps its
name, signature, instances and body; no target meaning changes.

## Old

The following definitions were in `Sheaf.Paper.PointTransportStrictQuotient`:

```lean
/-- Additivity of the published scalar restriction, exposed for termwise comparisons.
Source: Stacks Tag 07A6 (blueprint: lem-trf-point-transport-strict-quotient). -/
instance strictQuotientPointRestrictionAdditive (n : ℕ) :
    (pointUnitIntegralRestriction l E n).Additive :=
  inferInstanceAs ((ModuleCat.restrictScalars (pointReductionQuotient l E n)).Additive)

/-- The small localization of the coefficient-module category used by finite transport.
Source: Stacks Tag 05RU (blueprint: lem-trf-point-transport-strict-quotient). -/
instance strictQuotientPointModuleHasDerived (R : Type (u + 1)) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} R) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- The published identity-on-sections comparison in each degree of a complex.
Source: Stacks Tag 07A6 (blueprint: lem-trf-point-transport-strict-quotient). -/
def strictQuotientPointRestrictionComplexIso (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
        ((integralOperationsRestrict l E (Spec (.of D.k)) n).obj K) ≅
      ((pointUnitIntegralRestriction l E n).mapHomologicalComplex (.up ℤ)).obj
        (((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (pointUnitIntegralSectionsRestrictionIso D l E n).app (K.X i))
    (fun i j _ ↦ ((pointUnitIntegralSectionsRestrictionIso D l E n).hom.naturality
      (K.d i j)).symm)

/-- Exact scalar restriction with the localization sizes used by point transport.
Source: Stacks Tag 05RU (blueprint: lem-trf-point-transport-strict-quotient). -/
abbrev strictQuotientPointDerivedRestriction (n : ℕ) :=
  (pointUnitIntegralRestriction l E n).mapDerivedCategory.{u + 1, u + 1}

/-- Gamma(kappa) after sigma, restricted to the single integral coefficient ring.
The outer comparisons are the published identity-on-sections scalar comparisons.
Source: blueprint clause (3), simultaneous quotient transport
(blueprint: lem-trf-point-transport-strict-quotient). -/
def strictQuotientPointMap (n : ℕ)
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
        ((unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n).obj P) ⟶
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
        ((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).obj P) :=
  (strictQuotientPointRestrictionComplexIso D l E n
    ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P)).hom ≫
  ((pointUnitIntegralRestriction l E n).mapHomologicalComplex (.up ℤ)).map
    (frobeniusPointFiniteSigma D l E n
        ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P) ≫
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).map
          (inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n
            ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P))) ≫
  (strictQuotientPointRestrictionComplexIso D l E n
    (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).mapHomologicalComplex
      (.up ℤ)).obj ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P))).inv

/-- The canonical localization/sections comparison at a finite quotient, retaining
its integral action. Source: blueprint clause (3), finite evaluation
(blueprint: lem-trf-point-transport-strict-quotient). -/
def strictQuotientPointSectionsIso (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    DerivedCategory.Q.obj
        (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
          ((integralOperationsRestrict l E (Spec (.of D.k)) n).obj K)) ≅
      (strictQuotientPointDerivedRestriction l E n).obj
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
            (DerivedCategory.Q.obj K)) :=
  DerivedCategory.Q.mapIso
      (strictQuotientPointRestrictionComplexIso D l E n K) ≪≫
    ((pointUnitIntegralRestriction l E n).mapDerivedCategoryFactors.{u + 1, u + 1}.symm.app
      (((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).obj K)) ≪≫
    (strictQuotientPointDerivedRestriction l E n).mapIso
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.symm.app K)

/-- The canonical target comparison with the recorded intrinsic finite pullback.
Source: blueprint clause (3), finite evaluation
(blueprint: lem-trf-point-transport-strict-quotient). -/
def strictQuotientPointTargetIso (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    DerivedCategory.Q.obj
        (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
          ((integralOperationsRestrict l E (Spec (.of D.k)) n).obj
            (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n
              ).mapHomologicalComplex (.up ℤ)).obj K))) ≅
      (strictQuotientPointDerivedRestriction l E n).obj
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
            ((finiteDerivedPullback l E n (frobeniusPointIso D).hom).obj
              (DerivedCategory.Q.obj K))) := by
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  letI : (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    integralOperationsLevelPullback_additive l E (frobeniusPointIso D).hom n
  letI : PreservesFiniteLimits
      (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_limits l E (frobeniusPointIso D).hom n
  letI : PreservesFiniteColimits
      (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_colimits l E (frobeniusPointIso D).hom n
  exact
  strictQuotientPointSectionsIso D l E n
      (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).mapHomologicalComplex
        (.up ℤ)).obj K) ≪≫
    (strictQuotientPointDerivedRestriction l E n).mapIso
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.mapIso
          ((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n
            ).mapDerivedCategoryFactors.symm.app K)) ≪≫
    (strictQuotientPointDerivedRestriction l E n).mapIso
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.mapIso
          ((Functor.mapDerivedCategoryNatIso
            (inverseImageFiniteIntrinsicPullbackComparison (frobeniusPointIso D).hom
              (Padic.coefficientExtensionRing l E (n + 1)))).app (DerivedCategory.Q.obj K)))

/-- Standard localization for coherent integral-module towers. This chooses only
Mathlib's localization, not representatives of any transport.
Source: Stacks Tag 05RU (blueprint: lem-trf-point-transport-strict-quotient). -/
instance strictQuotientPointTowersHasDerived : HasDerivedCategory
    (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  HasDerivedCategory.standard _
```

## New

The same definitions and instances, with the bodies above unchanged, are in
`Sheaf.Paper.PointTransportStrictQuotientModels`. The item begins with:

```lean
public import Sheaf.Paper.PointTransportStrictQuotientModels
```

The definitions in the new model module are:

```lean
/-- Additivity of the published scalar restriction, exposed for termwise comparisons.
Source: Stacks Tag 07A6 (blueprint: lem-trf-point-transport-strict-quotient). -/
instance strictQuotientPointRestrictionAdditive (n : ℕ) :
    (pointUnitIntegralRestriction l E n).Additive :=
  inferInstanceAs ((ModuleCat.restrictScalars (pointReductionQuotient l E n)).Additive)

/-- The small localization of the coefficient-module category used by finite transport.
Source: Stacks Tag 05RU (blueprint: lem-trf-point-transport-strict-quotient). -/
instance strictQuotientPointModuleHasDerived (R : Type (u + 1)) [CommRing R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} R) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- The published identity-on-sections comparison in each degree of a complex.
Source: Stacks Tag 07A6 (blueprint: lem-trf-point-transport-strict-quotient). -/
def strictQuotientPointRestrictionComplexIso (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
        ((integralOperationsRestrict l E (Spec (.of D.k)) n).obj K) ≅
      ((pointUnitIntegralRestriction l E n).mapHomologicalComplex (.up ℤ)).obj
        (((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (pointUnitIntegralSectionsRestrictionIso D l E n).app (K.X i))
    (fun i j _ ↦ ((pointUnitIntegralSectionsRestrictionIso D l E n).hom.naturality
      (K.d i j)).symm)

/-- Exact scalar restriction with the localization sizes used by point transport.
Source: Stacks Tag 05RU (blueprint: lem-trf-point-transport-strict-quotient). -/
abbrev strictQuotientPointDerivedRestriction (n : ℕ) :=
  (pointUnitIntegralRestriction l E n).mapDerivedCategory.{u + 1, u + 1}

/-- Gamma(kappa) after sigma, restricted to the single integral coefficient ring.
The outer comparisons are the published identity-on-sections scalar comparisons.
Source: blueprint clause (3), simultaneous quotient transport
(blueprint: lem-trf-point-transport-strict-quotient)
(blueprint: def-trf-point-transport-strict-quotient-models). -/
def strictQuotientPointMap (n : ℕ)
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
        ((unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n).obj P) ⟶
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
        ((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).obj P) :=
  (strictQuotientPointRestrictionComplexIso D l E n
    ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P)).hom ≫
  ((pointUnitIntegralRestriction l E n).mapHomologicalComplex (.up ℤ)).map
    (frobeniusPointFiniteSigma D l E n
        ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P) ≫
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).map
          (inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n
            ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P))) ≫
  (strictQuotientPointRestrictionComplexIso D l E n
    (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).mapHomologicalComplex
      (.up ℤ)).obj ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P))).inv

/-- The canonical localization/sections comparison at a finite quotient, retaining
its integral action. Source: blueprint clause (3), finite evaluation
(blueprint: lem-trf-point-transport-strict-quotient). -/
def strictQuotientPointSectionsIso (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    DerivedCategory.Q.obj
        (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
          ((integralOperationsRestrict l E (Spec (.of D.k)) n).obj K)) ≅
      (strictQuotientPointDerivedRestriction l E n).obj
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
            (DerivedCategory.Q.obj K)) :=
  DerivedCategory.Q.mapIso
      (strictQuotientPointRestrictionComplexIso D l E n K) ≪≫
    ((pointUnitIntegralRestriction l E n).mapDerivedCategoryFactors.{u + 1, u + 1}.symm.app
      (((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapHomologicalComplex (.up ℤ)).obj K)) ≪≫
    (strictQuotientPointDerivedRestriction l E n).mapIso
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryFactors.symm.app K)

/-- The canonical target comparison with the recorded intrinsic finite pullback.
Source: blueprint clause (3), finite evaluation
(blueprint: lem-trf-point-transport-strict-quotient). -/
def strictQuotientPointTargetIso (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    DerivedCategory.Q.obj
        (((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
          ((integralOperationsRestrict l E (Spec (.of D.k)) n).obj
            (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n
              ).mapHomologicalComplex (.up ℤ)).obj K))) ≅
      (strictQuotientPointDerivedRestriction l E n).obj
        ((pointFiniteSections D.k
          (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj
            ((finiteDerivedPullback l E n (frobeniusPointIso D).hom).obj
              (DerivedCategory.Q.obj K))) := by
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  letI : (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    integralOperationsLevelPullback_additive l E (frobeniusPointIso D).hom n
  letI : PreservesFiniteLimits
      (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_limits l E (frobeniusPointIso D).hom n
  letI : PreservesFiniteColimits
      (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_colimits l E (frobeniusPointIso D).hom n
  exact
  strictQuotientPointSectionsIso D l E n
      (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).mapHomologicalComplex
        (.up ℤ)).obj K) ≪≫
    (strictQuotientPointDerivedRestriction l E n).mapIso
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.mapIso
          ((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n
            ).mapDerivedCategoryFactors.symm.app K)) ≪≫
    (strictQuotientPointDerivedRestriction l E n).mapIso
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.mapIso
          ((Functor.mapDerivedCategoryNatIso
            (inverseImageFiniteIntrinsicPullbackComparison (frobeniusPointIso D).hom
              (Padic.coefficientExtensionRing l E (n + 1)))).app (DerivedCategory.Q.obj K)))

/-- Standard localization for coherent integral-module towers. This chooses only
Mathlib's localization, not representatives of any transport.
Source: Stacks Tag 05RU (blueprint: lem-trf-point-transport-strict-quotient). -/
instance strictQuotientPointTowersHasDerived : HasDerivedCategory
    (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  HasDerivedCategory.standard _
```

The original declarations remain publicly available to every importer. The new
model module adds only a private proved construction for calculations with an
arbitrary finite complex. The changed comment on `strictQuotientPointMap` records
the model node; it does not change the construction. The original main theorem
retains its exact signature and now has a complete proof.

Because the statement of `pointTransport_strictQuotient` uses the moved
definitions, the item node `lem-trf-point-transport-strict-quotient` gains the
stmt_dep `def-trf-point-transport-strict-quotient-models` (reviewer fix); its
statement text and Lean signature are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointTransportStrictQuotient | E3 | Definitions re-exported; theorem proved. |
| Sheaf.Paper.PointTransportStrictQuotientModels | E3, new | Owns the unchanged definitions. |
| Sheaf.Paper.PointTransportStrictQuotientSections | E3, new | Proves the section formula. |
| Sheaf.Paper.PointTransportStrictQuotientIdentities | E3, new | Proves strict identities. |
| Sheaf.Paper.PointTransportStrictQuotientFiniteEvaluation | E3, new | Proves finite evaluation. |

A search of current `lean/Sheaf`, `lean/WeilConjectures`, and `quarantine/Sheaf`
finds no other module mentioning any moved declaration, and no direct importer
of the item. No existing consumer needs an adaptation. The pending parent DAG
uses are preserved; no module is withdrawn.

## Status

landed 20261026T194957-L-2608907 2026-10-26 (merge of deliver/E3/Sheaf.Paper.PointTransportStrictQuotient)
