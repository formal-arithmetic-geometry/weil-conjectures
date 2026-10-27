# identityOpenTermwiseDerivedAdjunction and identityOpenLocalizedDerivedUnit

## Reason

The original transported adjunction and associator-based localized unit cause kernel
checking of the complete normalization proof to exceed 60 seconds. Use the exact-left
canonical derived adjunction directly, and construct the localized unit by its components.
The proved generic `exactAdjunctionTransport` establishes equality of the two adjunction
constructions, including their units and counits. The component formula for the localized
unit is identical; naturality follows from the published UnitQ naturality and factorization.
All signatures and public imports remain unchanged. These are construction optimizations,
with no change to mathematical meaning.

## Old

```lean
def identityOpenTermwiseDerivedAdjunction {D Z : Scheme.{u}} (h : D ⟶ Z) :
    (upperStar Λ h).mapDerivedCategory ⊣ (lowerStar Λ h).rightDerivedFunctor :=
  (derivedUpperStarLowerStarAdjunction Λ h).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory Λ h)

def identityOpenLocalizedDerivedUnit {U D Z : Scheme.{u}}
    (j : U ⟶ Z) (h : D ⟶ Z) :
    (lowerStar Λ h).mapHomologicalComplex (.up ℤ) ⋙
        (upperStar Λ j).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (lowerStar Λ h).rightDerivedFunctor ⋙
        (upperStar Λ j).mapDerivedCategory :=
  Functor.whiskerLeft ((lowerStar Λ h).mapHomologicalComplex (.up ℤ))
      (upperStar Λ j).mapDerivedCategoryFactors.inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (identityOpenRightDerivedUnit Λ h)
      (upperStar Λ j).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom
```

## New

```lean
def identityOpenTermwiseDerivedAdjunction {D Z : Scheme.{u}} (h : D ⟶ Z) :
    (upperStar Λ h).mapDerivedCategory ⊣ (lowerStar Λ h).rightDerivedFunctor :=
  (upperStarLowerStarAdjunction Λ h).mapDerivedCategoryRightDerivedAdjunction

def identityOpenLocalizedDerivedUnit {U D Z : Scheme.{u}}
    (j : U ⟶ Z) (h : D ⟶ Z) :
    (lowerStar Λ h).mapHomologicalComplex (.up ℤ) ⋙
        (upperStar Λ j).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (lowerStar Λ h).rightDerivedFunctor ⋙
        (upperStar Λ j).mapDerivedCategory where
  app P := (upperStar Λ j).mapDerivedCategoryFactors.inv.app
      (((lowerStar Λ h).mapHomologicalComplex (.up ℤ)).obj P) ≫
    (upperStar Λ j).mapDerivedCategory.map ((lowerStar Λ h).rightDerivedFunctorUnitQ P)
  naturality P P' s := by
    dsimp only [Functor.comp_map]
    rw [Category.assoc, ← Functor.map_comp,
      ← (lowerStar Λ h).rightDerivedFunctorUnitQ_naturality s, Functor.map_comp]
    have hh := (upperStar Λ j).mapDerivedCategoryFactors.inv.naturality
      (((lowerStar Λ h).mapHomologicalComplex (.up ℤ)).map s)
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun f ↦ f ≫ (upperStar Λ j).mapDerivedCategory.map
        ((lowerStar Λ h).rightDerivedFunctorUnitQ P')) hh
```

Private proved categorical helpers share the structural arguments. Local irreducibility attributes and scoped backward elaboration options prevent
expansion during proof elaboration. They do not affect importers.

## Users

`tools/downstream.py --uses` finds no external occurrence of either repaired definition.
The two downstream modules use the unchanged pullback comparison. Their statements and
proofs require no adaptation. No source-library declaration is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | J8 | Equivalent constructions; proof. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | No adaptation needed. |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | unclaimed | No adaptation needed. |

## Status

landed 20261025T202318-L-2705785 2026-10-25 (merge of deliver/J8/Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization)
