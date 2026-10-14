# baseChangeTargetFunctorHigherImageIso and coefficient mapping APIs

## Reason

The original target comparison contains nested functor associators and a tactic-generated
conversion to explicit higher-image endpoints. The normalization proof exceeded the 60-second
single-file limit when checking these expressions. Constructing the same comparison by mapping
the pullback-single isomorphism directly, and writing the coefficient maps as direct terms,
reduced checking of this dependency to about 43 seconds and of the complete item to 35 seconds.
The adapted module is unclaimed. All existing signatures and visibility are preserved.
The file-local backward.isDefEq.respectTransparency option is false for these direct terms.

Every component of a functor associator is an identity, so the old target comparison's hom
and inv are exactly the nested mapped hom and inv of the pullback-single comparison. The two
coefficient mapping definitions have the identical nested functor expressions as before;
only the tactic-generated endpoint conversion is removed. Thus no definition changes its
mathematical meaning, and no target statement or hypothesis is changed. No importer needs
an adaptation, because the coefficient definitions are definitionally the same and the
canonical target comparison has the same components. Target statement meanings are preserved.

## Old

```lean
noncomputable def higherDirectImageMap {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ F') :
    higherDirectImage Λ h q F ⟶ higherDirectImage Λ h q F' := by
  let m := (DerivedCategory.Plus.homologyFunctor _ q).map
    (R+((h)_*[ModuleCat.{u + 1} Λ]).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map f))
  unfold higherDirectImage
  exact m

noncomputable def baseChangeTargetFunctorHigherImageIso
    {X T Y : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (baseChangeTargetFunctor Λ e h q).obj F ≅
      higherDirectImage Λ h q (((e)^*[ModuleCat.{u + 1} Λ]).obj F) := by
  let ii := (baseChangeTargetFunctorIso Λ e h q).app F
  unfold higherDirectImage
  exact ii

noncomputable def higherDirectImageMapIso {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ≅ F') :
    higherDirectImage Λ h q F ≅ higherDirectImage Λ h q F' := by
  let ii := (DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (R+((h)_*[ModuleCat.{u + 1} Λ]).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso f))
  unfold higherDirectImage
  exact ii
```

## New

```lean
noncomputable def higherDirectImageMap {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ F') :
    higherDirectImage Λ h q F ⟶ higherDirectImage Λ h q F' :=
  (DerivedCategory.Plus.homologyFunctor _ q).map
    (R+((h)_*[ModuleCat.{u + 1} Λ]).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map f))

noncomputable def baseChangeTargetFunctorHigherImageIso
    {X T Y : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (baseChangeTargetFunctor Λ e h q).obj F ≅
      higherDirectImage Λ h q (((e)^*[ModuleCat.{u + 1} Λ]).obj F) :=
  (DerivedCategory.Plus.homologyFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).mapIso
    (R+((h)_*[ModuleCat.{u + 1} Λ]).mapIso
      ((((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F))

noncomputable def higherDirectImageMapIso {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    {F F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ≅ F') :
    higherDirectImage Λ h q F ≅ higherDirectImage Λ h q F' :=
  (DerivedCategory.Plus.homologyFunctor _ q).mapIso
    (R+((h)_*[ModuleCat.{u + 1} Λ]).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso f))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.HigherDirectImageTransitionIsIsoOfLower | unclaimed | Direct definition bodies; unchanged signatures. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionHigherImage | K3 | Complete proof of the assigned normalization theorem. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | unclaimed | Same canonical arrows and statements; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageCoefficientSquare | unclaimed | Same canonical arrows and statements; no adaptation. |

The table contains every direct declaration user reported by downstream.py --uses for
these three definitions. All transitive downstream modules have unchanged APIs.

## Status

landed 20261014T200412-L-1836311 2026-10-14 (merge of deliver/K3/Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionHigherImage)
