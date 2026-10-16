# CoefficientCoherentPullbackData: cache the two field interfaces

## Reason

Instantiating the expanded coherence record at the concrete coefficient ring caused
kernel normalization through the internal-module and derived-category instances.
This happened even with temporary placeholders in both fields. The original construction
exceeded the single-file limit; raising that limit is not a repair.

Name the unchanged family type `CoefficientPullbackFamily` and unchanged square predicate
`CoefficientPullbackSquare`, and use those names both in the API's partial record and
in the two existing consumer records. The canonical family and its square theorem also
use exactly these cached types. The actual pullback isomorphisms are constructed by
restriction, conjugation and exact derivation. The item then compiles within the limit.

The original consumer compiled against the published API (22.4 seconds), but timed out
against the changed API with expanded field types. Reusing the cached types in its two
records makes it compile (31.5 seconds). Its only source changes are those four field
types. Its theorem proofs, right-mate condition, unit and counit equations are unchanged.
Both changed existing modules are unclaimed. The claimed C3 consumer compiles unchanged.

Each new type definition reduces to exactly its old field type, with no added hypotheses
and no changed equation. All existing declaration names, universes and visibility remain.
Target statements are unchanged; the definition review can check this definitional
identity directly. No object is chosen from a mere existence theorem.

## Old

```lean
/-- Inverse-image data and square coherence, without a condition on right mates. -/
structure CoefficientCoherentPullbackData (B : Type) [CommRing B]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) where
  pullback : ∀ {S T : Scheme.{u}} (h : S ⟶ T),
    D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h) ⋙
        F S ≅
      F T ⋙
        coefficientDerivedUpperStar Λ h
  square : ∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
      (K : FiniteDiscreteEtalePlus B Y),
    (F X').map
        ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).hom.app K) ≫
      (pullback g').hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).obj K) ≫
      (coefficientDerivedUpperStar Λ g').map
        ((pullback f).hom.app K) =
    (pullback f').hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj K) ≫
      (coefficientDerivedUpperStar Λ f').map
        ((pullback g).hom.app K) ≫
      (coefficientAmbientSquare Λ sq).hom.app
        ((F Y).obj K)


/-- Pullback comparisons with invertible right mates and coherent composition. -/
structure CoefficientComparisonData
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) where
  pullback : ∀ {S T : Scheme.{u}} (h : S ⟶ T),
    D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h) ⋙
        F S ≅
      F T ⋙
        coefficientDerivedUpperStar Λ h
  pushforward : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h],
    R+(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h) ⋙
        F T ≅
      F S ⋙
        coefficientDerivedLowerStar Λ h
  unit : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h]
      (K : FiniteDiscreteEtalePlus B T),
    (F T).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).unit.app K) ≫
      (pushforward h).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).obj K) ≫
      (coefficientDerivedLowerStar Λ h).map
        ((pullback h).hom.app K) =
    (coefficientDerivedAdjunction Λ h).unit.app
      ((F T).obj K)
  counit : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h]
      (K : FiniteDiscreteEtalePlus B S),
    (coefficientDerivedUpperStar Λ h).map
        ((pushforward h).hom.app K) ≫
      (coefficientDerivedAdjunction Λ h).counit.app
        ((F S).obj K) =
    (pullback h).inv.app
        (R+(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).obj K) ≫
      (F S).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).counit.app K)
  square : ∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
      (K : FiniteDiscreteEtalePlus B Y),
    (F X').map
        ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).hom.app K) ≫
      (pullback g').hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).obj K) ≫
      (coefficientDerivedUpperStar Λ g').map
        ((pullback f).hom.app K) =
    (pullback f').hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj K) ≫
      (coefficientDerivedUpperStar Λ f').map
        ((pullback g).hom.app K) ≫
      (coefficientAmbientSquare Λ sq).hom.app
        ((F Y).obj K)

/-- Coherent inverse-image comparisons whose canonical right mates are invertible. -/
structure CoefficientPullbackData
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) where
  pullback : ∀ {S T : Scheme.{u}} (h : S ⟶ T),
    D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h) ⋙
        F S ≅
      F T ⋙
        coefficientDerivedUpperStar Λ h
  rightMate : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h],
    IsIso (mateEquiv
      (Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)
      (coefficientDerivedAdjunction Λ h)
      (TwoSquare.mk _ _ _ _ (pullback h).inv)).natTrans
  square : ∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
      (K : FiniteDiscreteEtalePlus B Y),
    (F X').map
        ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).hom.app K) ≫
      (pullback g').hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).obj K) ≫
      (coefficientDerivedUpperStar Λ g').map
        ((pullback f).hom.app K) =
    (pullback f').hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj K) ≫
      (coefficientDerivedUpperStar Λ f').map
        ((pullback g).hom.app K) ≫
      (coefficientAmbientSquare Λ sq).hom.app
        ((F Y).obj K)

```

## New

```lean
/-- The family of inverse-image comparisons, with generic coefficient interfaces cached. -/
def CoefficientPullbackFamily (B : Type) [CommRing B]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) : Type _ :=
  ∀ {S T : Scheme.{u}} (h : S ⟶ T),
    D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h) ⋙
        F S ≅
      F T ⋙
        coefficientDerivedUpperStar Λ h

/-- Square coherence for a specified family of inverse-image comparisons. -/
def CoefficientPullbackSquare (B : Type) [CommRing B]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T)))
    (pullback : CoefficientPullbackFamily B Λ F) : Prop :=
  ∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
      {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g)
      (K : FiniteDiscreteEtalePlus B Y),
    (F X').map
        ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).hom.app K) ≫
      (pullback g').hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) f).obj K) ≫
      (coefficientDerivedUpperStar Λ g').map
        ((pullback f).hom.app K) =
    (pullback f').hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) g).obj K) ≫
      (coefficientDerivedUpperStar Λ f').map
        ((pullback g).hom.app K) ≫
      (coefficientAmbientSquare Λ sq).hom.app
        ((F Y).obj K)

/-- Inverse-image data and square coherence, without a condition on right mates. -/
structure CoefficientCoherentPullbackData (B : Type) [CommRing B]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) where
  pullback : CoefficientPullbackFamily B Λ F
  square : CoefficientPullbackSquare B Λ F pullback


/-- Pullback comparisons with invertible right mates and coherent composition. -/
structure CoefficientComparisonData
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) where
  pullback : CoefficientPullbackFamily B Λ F
  pushforward : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h],
    R+(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h) ⋙
        F T ≅
      F S ⋙
        coefficientDerivedLowerStar Λ h
  unit : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h]
      (K : FiniteDiscreteEtalePlus B T),
    (F T).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).unit.app K) ≫
      (pushforward h).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).obj K) ≫
      (coefficientDerivedLowerStar Λ h).map
        ((pullback h).hom.app K) =
    (coefficientDerivedAdjunction Λ h).unit.app
      ((F T).obj K)
  counit : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h]
      (K : FiniteDiscreteEtalePlus B S),
    (coefficientDerivedUpperStar Λ h).map
        ((pushforward h).hom.app K) ≫
      (coefficientDerivedAdjunction Λ h).counit.app
        ((F S).obj K) =
    (pullback h).inv.app
        (R+(Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).obj K) ≫
      (F S).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) h).counit.app K)
  square : CoefficientPullbackSquare B Λ F pullback

/-- Coherent inverse-image comparisons whose canonical right mates are invertible. -/
structure CoefficientPullbackData
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (F : ∀ T : Scheme.{u}, FiniteDiscreteEtalePlus B T ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) where
  pullback : CoefficientPullbackFamily B Λ F
  rightMate : ∀ {S T : Scheme.{u}} (h : S ⟶ T) [QuasiCompact h] [QuasiSeparated h],
    IsIso (mateEquiv
      (Etale.derivedUpperStarLowerStarAdjunctionPlus
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) h)
      (coefficientDerivedAdjunction Λ h)
      (TwoSquare.mk _ _ _ _ (pullback h).inv)).natTrans
  square : CoefficientPullbackSquare B Λ F pullback

```

## Users

`tools/downstream.py` listed the following downstream modules and named users.
The API and the adapted consumer are also listed. Only the API, its unclaimed consumer
and the assigned item change. The direct importers were checked separately.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Name the old field types and reuse them in the partial record. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Replace four expanded field types by their definitionally equal cached names; all proofs and remaining declarations unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | A4 | Construct the record from the specified family and its square theorem; signature unchanged. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | C3 | Original source compiled unchanged against the adapted consumer. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | D2 | Original source compiled unchanged against the adapted API. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Same mathematical interface; no source adaptation or statement change. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Same mathematical interface; no source adaptation or statement change. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Same mathematical interface; no source adaptation or statement change. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Same mathematical interface; no source adaptation or statement change. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Same mathematical interface; no source adaptation or statement change. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Same mathematical interface; no source adaptation or statement change. |
| TargetsCheck | unclaimed | Same mathematical interface; no source adaptation or statement change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same mathematical interface; no source adaptation or statement change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same mathematical interface; no source adaptation or statement change. |

## Status

landed 20261016T155153-L-839662 2026-10-16 (merge of deliver/A4/Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks)
