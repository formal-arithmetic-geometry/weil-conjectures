# chartUnitPullback

## Reason

Check the canonical unit-pullback composite at an abstract coefficient ring before
specializing to `P.Coefficient`. The local function has exactly the previous three
factors. Unfolding `smoothPurityPullback` and `sfFixedDerivedPullback`, followed by
beta and zeta reduction, gives the old value. This is a definitionally identical
map with a smaller conversion problem during type checking. No data or statement
changes, and no private declaration occurs in this public definition.

## Old

```lean
def chartUnitPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (P.smoothPurityPullback f).obj
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit P.Coefficient Y)) ≅
      𝟙_ (_root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) :=
  (P.smoothPurityPullback f).mapIso (projectionUnitRaw P.Coefficient Y) ≪≫
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) f).symm.app _ ≪≫
    ProEtale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) f
```

## New

```lean
def chartUnitPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (P.smoothPurityPullback f).obj
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit P.Coefficient Y)) ≅
      𝟙_ (_root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))) :=
  let unitPullback (A : Type (u + 1)) [CommRing A]
      {S T : Scheme.{u}} (g : S ⟶ T) :
      (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit A T)) ≅
        𝟙_ (_root_.DerivedCategory
          (Sheaf (Scheme.ProEt.topology S) (ModuleCat.{u + 1} A))) :=
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.mapIso
        (projectionUnitRaw A T) ≪≫
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) g).symm.app _ ≪≫
      ProEtale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) g
  unitPullback P.Coefficient f
```

## Users

The declaration uses were read and the module claims checked. Both consumers
receive the same definitionally equal map, so neither needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | abstract-ring checking before specialization |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | definitionally identical map |

## Status

landed 20261026T002820-L-117385 2026-10-26 (merge of deliver/T5/Sheaf.Paper.DiagonalDncChartNormalization)
