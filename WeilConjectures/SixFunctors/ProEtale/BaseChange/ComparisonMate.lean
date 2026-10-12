/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonIso
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeMate

/-!
# The comparison of direct images is the mate of the comparison of pullbacks

For a quasi-compact quasi-separated morphism `f : X ⟶ Y`, the comparison isomorphism
`ν_Y^* Rf_* ≅ Rf_* ν_X^*` (`AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonIso'`) is
the mate, under the derived adjunctions `f^* ⊣ Rf_*` (étale, bounded below) and
`Lf^* ⊣ Rf_*` (pro-étale), of the inverse of the comparison isomorphism
`ν_X^* f^* ≅ Lf^* ν_Y^*` (`AlgebraicGeometry.ProEtale.leftDerivedUpperStarComparisonIso`).

The underived counterpart (`AlgebraicGeometry.ProEtale.lowerStarComparisonUpperStarBaseChange_eq`)
is formal: both underived comparisons are obtained by taking mates of the same isomorphism
`f_* ν_{X,*} ≅ ν_{Y,*} f_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [HasDerivedCategory C₄]
  {L : C₂ ⥤ C₁} {L' : C₄ ⥤ C₃} {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
  [L.Additive] [L'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- The square `G⁺ ⋙ L'⁺ ≅ L⁺ ⋙ G'⁺` of functors on bounded below derived categories induced
by a square `σ : G ⋙ L' ≅ L ⋙ G'` of exact functors. -/
noncomputable abbrev mapDerivedCategoryPlusSquareIso (σ : G ⋙ L' ≅ L ⋙ G') :
    G.mapDerivedCategoryPlus ⋙ L'.mapDerivedCategoryPlus ≅
      L.mapDerivedCategoryPlus ⋙ G'.mapDerivedCategoryPlus :=
  (mapDerivedCategoryPlusCompIso G L').symm ≪≫ mapDerivedCategoryPlusNatIso σ ≪≫
    mapDerivedCategoryPlusCompIso L G'

/-- The square `G⁺ ⋙ L'⁺ ≅ L⁺ ⋙ G'⁺` induced by `σ` is computed by `σ` on complexes. -/
@[reassoc]
lemma mapDerivedCategoryPlusSquareIso_hom_app_factorsh (σ : G ⋙ L' ≅ L ⋙ G')
    (N : HomotopyCategory.Plus C₂) :
    (mapDerivedCategoryPlusSquareIso σ).hom.app (DerivedCategory.Plus.Qh.obj N) ≫
        G'.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        G'.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj N) =
      L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ.hom).app N) := by
  have h₁ := mapDerivedCategoryPlusCompIso_hom_app_factorsh L G' N
  have h₂ := mapDerivedCategoryPlusNatIso_hom_app_factorsh σ N
  have h₃ := mapDerivedCategoryPlusCompIso_hom_app_factorsh G L' N
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [h₁, reassoc_of% h₂, ← h₃, Iso.inv_hom_id_app_assoc]
  simp only [Category.assoc]

/-- The image under `DerivedCategory.Plus.ι` of the inverse of the composition isomorphism of
`mapDerivedCategoryPlus` is the inverse of the composition isomorphism of
`mapDerivedCategory`. -/
lemma ι_map_mapDerivedCategoryPlusCompIso_inv_app (X : DerivedCategory.Plus C₂) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusCompIso G L').inv.app X) =
      (mapDerivedCategoryCompIso G L').inv.app (DerivedCategory.Plus.ι.obj X) := by
  rw [← cancel_epi (DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusCompIso G L').hom.app X)),
    ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id,
    ι_map_mapDerivedCategoryPlusCompIso_hom_app, Iso.hom_inv_id_app]
  rfl

/-- The image under `DerivedCategory.Plus.ι` of the square induced by `σ` on bounded below
derived categories is the square induced by `σ` on unbounded derived categories. -/
lemma ι_map_mapDerivedCategoryPlusSquareIso_hom_app (σ : G ⋙ L' ≅ L ⋙ G')
    (X : DerivedCategory.Plus C₂) :
    DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusSquareIso σ).hom.app X) =
      (mapDerivedCategoryCompIso G L').inv.app (DerivedCategory.Plus.ι.obj X) ≫
        (mapDerivedCategoryNatIso σ).hom.app (DerivedCategory.Plus.ι.obj X) ≫
        (mapDerivedCategoryCompIso L G').hom.app (DerivedCategory.Plus.ι.obj X) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    ι_map_mapDerivedCategoryPlusCompIso_inv_app, ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    ι_map_mapDerivedCategoryPlusCompIso_hom_app]

end CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Underived

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The underived base change morphism `ν_Y^* f_* ⟶ f_* ν_X^*` is the mate, under the
adjunctions `f^* ⊣ f_*` on the étale and on the pro-étale sites, of the comparison
`ν_Y^* ⋙ f^* ≅ f^* ⋙ ν_X^*` of pullbacks. -/
lemma lowerStarComparisonUpperStarBaseChange_eq :
    lowerStarComparisonUpperStarBaseChange f A =
      mateEquiv (Etale.upperStarLowerStarAdjunction A f)
        (ProEtale.upperStarLowerStarAdjunction A f)
        (comparisonUpperStarCompUpperStarIso A f).hom := by
  refine ((mateEquiv (comparisonAdjunction A X) (comparisonAdjunction A Y)).symm_apply_eq).2 ?_
  refine Eq.trans ?_ (iterated_mateEquiv_conjugateEquiv (Etale.upperStarLowerStarAdjunction A f)
    (ProEtale.upperStarLowerStarAdjunction A f) (comparisonAdjunction A Y)
    (comparisonAdjunction A X) (comparisonUpperStarCompUpperStarIso A f).hom).symm
  exact congrArg Iso.hom ((conjugateIsoEquiv
    ((Etale.upperStarLowerStarAdjunction A f).comp (comparisonAdjunction A X))
    ((comparisonAdjunction A Y).comp (ProEtale.upperStarLowerStarAdjunction A f))).apply_symm_apply
      (lowerStarCompComparisonLowerStarIso f A).symm).symm

end Underived

end ProEtale

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

section Derived

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The image under `DerivedCategory.Plus.ι` of the counit of the bounded below derived adjunction
`Lf^* ⊣ Rf_*` on pro-étale sheaves is the counit of the unbounded derived adjunction, up to the
identifications `Lf^* ≅ D(f^*)` and `ι ∘ R⁺f_* ≅ Rf_* ∘ ι`. -/
lemma ι_map_derivedPlus_counit_app
    (Z : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.Plus.ι.map
        ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus.counit.app
          Z) =
      D(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
          ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusCompatibility.hom.app
            Z) ≫
        (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).inv.app _ ≫
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
          (DerivedCategory.Plus.ι.obj Z) := by
  rw [← Adjunction.derivedAdjunctionPlus_eq_derivedPlus, Adjunction.derivedAdjunctionPlus,
    Adjunction.map_restrictFullyFaithful_counit_app, Adjunction.ofNatIsoLeft_counit]
  simp [Functor.mapDerivedCategoryPlusCompatibility, derivedUpperStarLowerStarAdjunction,
    ProEtale.leftDerivedUpperStarIsoMapDerivedCategory]

/-- The square `D⁺(ν_Y) ⋙ D⁺(f^*) ≅ D⁺(f^*) ⋙ D⁺(ν_X)` induced by the comparison
`ν_Y^* f^* ≅ f^* ν_X^*` of pullbacks. -/
noncomputable abbrev comparisonUpperStarPlusSquareIso :
    D+(ν^*(Y)[ModuleCat.{u + 1} Λ]) ⋙ D+(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f) ≅
      D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f) ⋙ D+(ν^*(X)[ModuleCat.{u + 1} Λ]) :=
  Functor.mapDerivedCategoryPlusSquareIso
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f)

/-- The comparison `ν_X^* f^* ≅ Lf^* ν_Y^*` composed with `Lf^* ≅ D(f^*)` is inverse to the
square `comparisonUpperStarPlusSquareIso` induced on bounded below derived categories. -/
lemma leftDerivedUpperStarComparisonIso_hom_app_comp
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarComparisonIso f Λ).hom.app K ≫
        (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).hom.app _ ≫
        DerivedCategory.Plus.ι.map ((comparisonUpperStarPlusSquareIso Λ f).hom.app K) =
      𝟙 _ := by
  rw [Functor.ι_map_mapDerivedCategoryPlusSquareIso_hom_app]
  simp [leftDerivedUpperStarComparisonIso, Functor.mapDerivedCategoryPlusCompatibility,
    Functor.mapDerivedCategoryNatIso_symm]

/-- Blueprint `prop-weil-pbc-comparison-direct-image` (compatibility with the counits): the
comparison `ν_Y^* Rf_* ≅ Rf_* ν_X^*` is the mate of the comparison `ν_X^* f^* ≅ Lf^* ν_Y^*`, in
the transposed form: `ν_X^* f^* Rf_* M ≅ Lf^* ν_Y^* Rf_* M ⟶ Lf^* Rf_* ν_X^* M ⟶ ν_X^* M` is
`ν_X^*` of the counit of `f^* ⊣ Rf_*`. -/
theorem leftDerivedUpperStarComparisonIso_hom_app_comp_counit [QuasiCompact f]
    [QuasiSeparated f]
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarComparisonIso f Λ).hom.app
        (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        ((rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ)).hom.app M) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj (DerivedCategory.Plus.ι.obj M)) =
    D(ν^*(X)[ModuleCat.{u + 1} Λ]).map (DerivedCategory.Plus.ι.map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app M)) := by
  -- the bounded below statement
  have hP := Adjunction.rightDerivedFunctorPlusBaseChange_mateEquiv_counit
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (TwoSquare.mk _ _ _ _ (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).hom)
    (TwoSquare.mk _ _ _ _ (comparisonUpperStarPlusSquareIso Λ f).hom)
    (Functor.mapDerivedCategoryPlusSquareIso_hom_app_factorsh _) M
  have hc : Functor.rightDerivedFunctorPlusBaseChange
      (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
        (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
        (TwoSquare.mk _ _ _ _
          (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).hom)).natTrans =
      (rightDerivedLowerStarComparisonPlusIso f (ModuleCat.{u + 1} Λ)).hom := by
    rw [rightDerivedLowerStarComparisonPlusIso, asIso_hom,
      lowerStarComparisonUpperStarBaseChange_eq]
    rfl
  rw [hc] at hP
  replace hP := congrArg DerivedCategory.Plus.ι.map hP
  rw [Functor.map_comp, Functor.map_comp, ι_map_derivedPlus_counit_app] at hP
  -- the unbounded statement
  have hd := leftDerivedUpperStarComparisonIso_hom_app_comp Λ f
    (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj M)
  rw [← NatIso.naturality_2 (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} Λ) f)]
  simp only [rightDerivedLowerStarComparisonIso', Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.mapDerivedCategoryPlusCompatibility,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Functor.map_id, Category.id_comp,
    Category.comp_id, Functor.map_comp, Category.assoc]
  rw [Etale.derivedUpperStarLowerStarAdjunctionPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  erw [hP]
  rw [Functor.map_comp, reassoc_of% hd]
  rfl

end Derived

end ProEtale

end AlgebraicGeometry
