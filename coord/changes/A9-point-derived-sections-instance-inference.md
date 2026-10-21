# WeilConjectures.pointUnitIntegralDerivedSectionsRestrictionIso

## Reason

The original integral comparison spent about 26 seconds inferring additivity of
module restriction. Its maps preserve addition by reflexivity; both comparisons now
supply this direct proof and the existing coefficient-specific exactness witnesses.
Their three factors remain the original derived composition isomorphisms and the
localization of the identity-on-sections isomorphism. `convert!` discharges only their
definitional equalities.

The finite derived module restriction and its factorization now pass the existing
Grothendieck-derived-category instances explicitly, avoiding search through two
coefficient categories. These are the same instances used by their original local
`letI` expressions and by `pointUnitFiniteQ`. No functor, localization or comparison
map changes. Added additive/exactness witnesses are proofs of propositions and agree
by proof irrelevance. No target or downstream signature changes. The semantic review
checks these identical constructions with explicit instance arguments.

## Old

```lean
def pointUnitIntegralDerivedSectionsRestrictionIso (n : ℕ) :
    scalarReductionDerivedRestriction l E (Spec (.of D.k)) n ⋙
        (pointIntegralSections l E D.k).mapDerivedCategory ≅
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory ⋙
        pointUnitIntegralDerivedRestriction l E n :=
  letI : (pointUnitIntegralRestriction l E n).Additive :=
    inferInstanceAs ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointReductionQuotient l E n)).Additive)
  letI : (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).Additive :=
    pointFiniteSectionsAdditive _ _
  letI : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
      pointUnitIntegralRestriction l E n).Additive := inferInstance
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pointUnitIntegralRestriction l E n) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pointUnitIntegralRestriction l E n) := comp_preservesFiniteColimits _ _
  letI : PreservesFiniteLimits
      (scalarReductionRestriction l E (Spec (.of D.k)) n ⋙ pointIntegralSections l E D.k) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (scalarReductionRestriction l E (Spec (.of D.k)) n ⋙ pointIntegralSections l E D.k) :=
    comp_preservesFiniteColimits _ _
  (Functor.mapDerivedCategoryCompIso
    (scalarReductionRestriction l E (Spec (.of D.k)) n)
    (pointIntegralSections l E D.k)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointUnitIntegralSectionsRestrictionIso D l E n) ≪≫
    Functor.mapDerivedCategoryCompIso
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
      (pointUnitIntegralRestriction l E n)
```

```lean
def pointUnitFiniteDerivedSectionsRestrictionIso (n j : ℕ) (h : j ≤ n) :
    pointUnitFiniteDerivedRestriction D l E n j h ⋙
        pointFiniteReductionSections D.k l E n ≅
      pointFiniteReductionSections D.k l E j ⋙
        pointUnitFiniteDerivedModuleRestriction l E n j h :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E j)
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E n)
  letI : (pointUnitFiniteModuleRestriction l E n j h).Additive :=
    inferInstanceAs ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointFiniteReductionRingMap l E n j h)).Additive)
  letI : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).Additive :=
    pointFiniteSectionsAdditive _ _
  letI : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j)).Additive :=
    pointFiniteSectionsAdditive _ _
  letI : PreservesFiniteLimits
      (pointUnitFiniteRestriction D l E n j h ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (pointUnitFiniteRestriction D l E n j h ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :=
    comp_preservesFiniteColimits _ _
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j) ⋙
        pointUnitFiniteModuleRestriction l E n j h) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j) ⋙
        pointUnitFiniteModuleRestriction l E n j h) := comp_preservesFiniteColimits _ _
  (Functor.mapDerivedCategoryCompIso (pointUnitFiniteRestriction D l E n j h)
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointUnitFiniteSectionsRestrictionIso D l E n j h) ≪≫
    Functor.mapDerivedCategoryCompIso
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j))
      (pointUnitFiniteModuleRestriction l E n j h)
```

```lean
def pointUnitFiniteDerivedModuleRestriction (n j : ℕ) (h : j ≤ n) :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E j)
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E n)
  (pointUnitFiniteModuleRestriction l E n j h).mapDerivedCategory
```

```lean
def pointUnitFiniteModuleFactors (n j : ℕ) (h : j ≤ n) :=
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E j)
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E n)
  (pointUnitFiniteModuleRestriction l E n j h).mapDerivedCategoryFactors
```

## New

```lean
def pointUnitIntegralDerivedSectionsRestrictionIso (n : ℕ) :
    scalarReductionDerivedRestriction l E (Spec (.of D.k)) n ⋙
        (pointIntegralSections l E D.k).mapDerivedCategory ≅
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory ⋙
        pointUnitIntegralDerivedRestriction l E n := by
  letI : PreservesFiniteLimits (scalarReductionRestriction l E (Spec (.of D.k)) n) :=
    scalarReductionRestrictionLimits l E (Spec (.of D.k)) n
  letI : PreservesFiniteColimits (scalarReductionRestriction l E (Spec (.of D.k)) n) :=
    scalarReductionRestrictionColimits l E (Spec (.of D.k)) n
  letI : PreservesFiniteLimits (pointIntegralSections l E D.k) :=
    pointReductionIntegralLimits D l E
  letI : PreservesFiniteColimits (pointIntegralSections l E D.k) :=
    pointReductionIntegralColimits D l E
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))) :=
    pointFiniteReductionSectionsLimits D.k l E (n + 1)
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))) :=
    pointFiniteReductionSectionsColimits D.k l E (n + 1)
  letI : (pointUnitIntegralRestriction l E n).Additive := ⟨by intros; rfl⟩
  letI : (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).Additive :=
    pointFiniteSectionsAdditive _ _
  letI : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
      pointUnitIntegralRestriction l E n).Additive := inferInstance
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pointUnitIntegralRestriction l E n) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pointUnitIntegralRestriction l E n) := comp_preservesFiniteColimits _ _
  letI : PreservesFiniteLimits
      (scalarReductionRestriction l E (Spec (.of D.k)) n ⋙ pointIntegralSections l E D.k) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (scalarReductionRestriction l E (Spec (.of D.k)) n ⋙ pointIntegralSections l E D.k) :=
    comp_preservesFiniteColimits _ _
  convert! ((Functor.mapDerivedCategoryCompIso
    (scalarReductionRestriction l E (Spec (.of D.k)) n)
    (pointIntegralSections l E D.k)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointUnitIntegralSectionsRestrictionIso D l E n) ≪≫
    Functor.mapDerivedCategoryCompIso
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
      (pointUnitIntegralRestriction l E n)) using 3
```

```lean
def pointUnitFiniteDerivedSectionsRestrictionIso (n j : ℕ) (h : j ≤ n) :
    pointUnitFiniteDerivedRestriction D l E n j h ⋙
        pointFiniteReductionSections D.k l E n ≅
      pointFiniteReductionSections D.k l E j ⋙
        pointUnitFiniteDerivedModuleRestriction l E n j h := by
  letI : PreservesFiniteLimits (pointUnitFiniteRestriction D l E n j h) :=
    pointUnitFiniteRestrictionLimits D l E n j h
  letI : PreservesFiniteColimits (pointUnitFiniteRestriction D l E n j h) :=
    pointUnitFiniteRestrictionColimits D l E n j h
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :=
    pointFiniteReductionSectionsLimits D.k l E n
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :=
    pointFiniteReductionSectionsColimits D.k l E n
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j)) :=
    pointFiniteReductionSectionsLimits D.k l E j
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j)) :=
    pointFiniteReductionSectionsColimits D.k l E j
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E j)
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (pointFiniteReductionModules l E n)
  letI : (pointUnitFiniteModuleRestriction l E n j h).Additive := ⟨by intros; rfl⟩
  letI : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).Additive :=
    pointFiniteSectionsAdditive _ _
  letI : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j)).Additive :=
    pointFiniteSectionsAdditive _ _
  letI : PreservesFiniteLimits
      (pointUnitFiniteRestriction D l E n j h ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (pointUnitFiniteRestriction D l E n j h ⋙
        pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)) :=
    comp_preservesFiniteColimits _ _
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j) ⋙
        pointUnitFiniteModuleRestriction l E n j h) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j) ⋙
        pointUnitFiniteModuleRestriction l E n j h) := comp_preservesFiniteColimits _ _
  convert! ((Functor.mapDerivedCategoryCompIso (pointUnitFiniteRestriction D l E n j h)
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E n))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointUnitFiniteSectionsRestrictionIso D l E n j h) ≪≫
    Functor.mapDerivedCategoryCompIso
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E j))
      (pointUnitFiniteModuleRestriction l E n j h)) using 3
```

```lean
def pointUnitFiniteDerivedModuleRestriction (n j : ℕ) (h : j ≤ n) :=
  @Functor.mapDerivedCategory
    (pointFiniteReductionModules l E j) inferInstance inferInstance
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (pointFiniteReductionModules l E j))
    (pointFiniteReductionModules l E n) inferInstance inferInstance
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (pointFiniteReductionModules l E n))
    (pointUnitFiniteModuleRestriction l E n j h) inferInstance inferInstance inferInstance
```

```lean
def pointUnitFiniteModuleFactors (n j : ℕ) (h : j ≤ n) :=
  @Functor.mapDerivedCategoryFactors
    (pointFiniteReductionModules l E j) inferInstance inferInstance
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (pointFiniteReductionModules l E j))
    (pointFiniteReductionModules l E n) inferInstance inferInstance
    (HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (pointFiniteReductionModules l E n))
    (pointUnitFiniteModuleRestriction l E n j h) inferInstance inferInstance inferInstance
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PointReductionUnits | A9 | Same data with explicit instances. |
| Sheaf.Paper.PointReductionUnitNormalization | unclaimed | Same comparisons; no adaptation. |

## Status

landed 20261021T002923-L-1578406 2026-10-21 (merge of deliver/A9/Sheaf.Paper.PointReductionUnits)
