/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonMate
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.PullbackSquare
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPasting

/-!
# Transport identifies the exchange map

Conjugating the étale exchange map `g^* Rf_* ⟶ Rf'_* g'^*` of a square by the comparison
isomorphisms of `WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonIso` gives the
pro-étale exchange map (blueprint `lem-weil-pbc-transport-identifies-exchange`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

namespace ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The comparison `ν_{Y'}^* g^* ≅ Lg^* ν_Y^*` is the square induced by the underived comparison
`AlgebraicGeometry.ProEtale.comparisonUpperStarCompUpperStarIso`, followed by `D(g^*) ≅ Lg^*`. -/
lemma leftDerivedUpperStarComparisonIso_hom_app (h : Y' ⟶ Y)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarComparisonIso h Λ).hom.app M =
      (Functor.mapDerivedCategorySquareIso
          (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) h).symm).hom.app
          (DerivedCategory.Plus.ι.obj M) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) h).inv.app _ := by
  simp [leftDerivedUpperStarComparisonIso, Functor.mapDerivedCategoryPlusCompatibility,
    Functor.mapDerivedCategorySquareIso]

/-- The comparisons `ν^* h^* ≅ Lh^* ν^*` of the four sides of a commutative square are
compatible with the identifications `θ : f'^* g^* ≅ g'^* f^*` of the étale and of the
pro-étale derived pullbacks (blueprint `lem-weil-pbc-comparison-pullback`). -/
lemma leftDerivedUpperStarComparisonIso_square (sq : CommSq g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D(ν^*(X')[ModuleCat.{u + 1} Λ]).map (DerivedCategory.Plus.ι.map
        ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq).hom.app M)) ≫
      (leftDerivedUpperStarComparisonIso g' Λ).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
        ((leftDerivedUpperStarComparisonIso f Λ).hom.app M) =
    (leftDerivedUpperStarComparisonIso f' Λ).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f').map
        ((leftDerivedUpperStarComparisonIso g Λ).hom.app M) ≫
      (ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq).hom.app
        (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Plus.ι.obj M)) := by
  have hcube := Functor.mapDerivedCategorySquareIso_cube
    (Etale.squareUpperStarIso (ModuleCat.{u + 1} Λ) sq)
    (ProEtale.upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w.symm)
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g).symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f').symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) g').symm
    (fun k ↦ by
      simpa only [Iso.symm_hom] using
        comparisonUpperStarCompUpperStarIso_square (ModuleCat.{u + 1} Λ) sq k)
    (DerivedCategory.Plus.ι.obj M)
  have hsq := ProEtale.mapDerivedCategorySquareIso_upperStarCompIso_hom_app
    (ModuleCat.{u + 1} Λ) sq (D(ν^*(Y)[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Plus.ι.obj M))
  rw [Etale.ι_map_pullbackSquareComparison_hom_app]
  simp only [leftDerivedUpperStarComparisonIso_hom_app, Functor.map_comp, Category.assoc]
  erw [← (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g').inv.naturality_assoc,
    ← (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f').inv.naturality_assoc]
  erw [reassoc_of% hcube]
  simp only [Category.assoc]
  erw [hsq]

/-- Blueprint `lem-weil-pbc-transport-identifies-exchange` (subsection
`sk-thm-properbasechange`): for a Cartesian square

```
  X' ──g'──▶ X
  │          │
  f'         f
  ▼          ▼
  Y' ──g───▶ Y
```

with `f` (hence `f'`) quasi-compact and quasi-separated, and `L ∈ D⁺(X_ét, Λ)`, conjugating
the étale exchange map `g^* Rf_* L ⟶ Rf'_* g'^* L` by the comparison isomorphisms
`ν_{Y'}^* g^* Rf_* L ≅ Lg^* Rf_* ν_X^* L` and `ν_{Y'}^* Rf'_* g'^* L ≅ Rf'_* Lg'^* ν_X^* L`
(`AlgebraicGeometry.ProEtale.baseChangeSourceComparisonIso`,
`AlgebraicGeometry.ProEtale.baseChangeTargetComparisonIso`) gives the pro-étale exchange map
at `ν_X^* L`. -/
theorem comparison_derivedBaseChangeMap [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f']
    [QuasiSeparated f'] (sq : IsPullback g' f' f g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D(ν^*(Y')[ModuleCat.{u + 1} Λ]).map
        (DerivedCategory.Plus.ι.map ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L)) ≫
      (baseChangeTargetComparisonIso g' f' Λ).hom.app L =
    (baseChangeSourceComparisonIso f g Λ).hom.app L ≫
      (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj (DerivedCategory.Plus.ι.obj L)) := by
  -- the comparison of direct images is the mate of the comparison of pullbacks
  have hA : ∀ {X₀ Y₀ : Scheme.{u}} (h : X₀ ⟶ Y₀) [QuasiCompact h] [QuasiSeparated h]
      (M : DerivedCategory.Plus (Sheaf X₀.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) h).map
          ((rightDerivedLowerStarComparisonIso' h (ModuleCat.{u + 1} Λ)).hom.app M) ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).counit.app
          (D(ν^*(X₀)[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Plus.ι.obj M)) =
      (leftDerivedUpperStarComparisonIso h Λ).inv.app
          (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) h).obj M) ≫
        D(ν^*(X₀)[ModuleCat.{u + 1} Λ]).map (DerivedCategory.Plus.ι.map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) h).counit.app
            M)) := by
    intro X₀ Y₀ h _ _ M
    rw [← cancel_epi ((leftDerivedUpperStarComparisonIso h Λ).hom.app _),
      Iso.hom_inv_id_app_assoc]
    exact leftDerivedUpperStarComparisonIso_hom_app_comp_counit Λ h M
  -- the étale exchange map is the mate of `θ_E`
  have hE : D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f').map
        ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app L) ≫
      (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f').counit.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g').obj L) =
      (Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app
          (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj L) ≫
        D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g').map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app
            L) := by
    rw [Etale.baseChange_app_eq_mateEquiv, Etale.derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus,
      Etale.derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus]
    exact mateEquiv_counit _ _ _ L
  -- the pro-étale exchange map is the mate of `θ_P`
  have hP := mateEquiv_counit (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f')
    (ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom
    ((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj (DerivedCategory.Plus.ι.obj L))
  -- the comparisons of pullbacks are compatible with `θ_E` and `θ_P`
  have hC := leftDerivedUpperStarComparisonIso_square Λ sq.toCommSq
    (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj L)
  have hC' : (leftDerivedUpperStarComparisonIso f' Λ).inv.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj
          (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj L)) ≫
      D(ν^*(X')[ModuleCat.{u + 1} Λ]).map (DerivedCategory.Plus.ι.map
        ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app
          (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj L))) ≫
      (leftDerivedUpperStarComparisonIso g' Λ).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj
          (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj L)) =
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f').map
          ((leftDerivedUpperStarComparisonIso g Λ).hom.app
            (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj L)) ≫
        (ProEtale.leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app _ ≫
        L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
          ((leftDerivedUpperStarComparisonIso f Λ).inv.app
            (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj L)) := by
    rw [← cancel_epi ((leftDerivedUpperStarComparisonIso f' Λ).hom.app _),
      Iso.hom_inv_id_app_assoc, ← cancel_mono (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
        ((leftDerivedUpperStarComparisonIso f Λ).hom.app
          (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj L)))]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id,
      Category.comp_id]
    exact hC
  -- transpose both sides under `Lf'^* ⊣ Rf'_*`
  apply ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f').homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, baseChangeTargetComparisonIso,
    baseChangeSourceComparisonIso, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc, Functor.comp_obj]
  erw [Adjunction.counit_naturality, hA f', hP]
  sorry

end ProEtale

end AlgebraicGeometry
