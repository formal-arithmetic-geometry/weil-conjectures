/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonUnit
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerDefs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Transport of relative units and Kummer adjoints along the étale/pro-étale comparison

For a quasi-compact quasi-separated morphism, invertibility of `Hⁿ` of the étale adjoints
(units, Kummer edge maps) implies invertibility of `Hⁿ` of the pro-étale ones, and vanishing
of étale higher direct images implies vanishing of the pro-étale ones
(blueprint: lem-pur-relative-kummer-arbitrary-base-maps, comparison paragraph).
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

/-- **Transport of `homEquiv` along comparison functors.** In the setting of
`CategoryTheory.Adjunction.map_unit_comp_eq_unit`, once the units are compatible (`hu`), the
`homEquiv` of `d` at `a⁻¹ ≫ A₁ φ` is `A₀` of the `homEquiv` of `e` at `φ`, followed by `b`. -/
theorem CategoryTheory.Adjunction.homEquiv_inv_app_comp_map {E₀ E₁ P₀ P₁ : Type*}
    [Category E₀] [Category E₁] [Category P₀] [Category P₁]
    {l : E₀ ⥤ E₁} {r : E₁ ⥤ E₀} {p : P₀ ⥤ P₁} {s : P₁ ⥤ P₀} (e : l ⊣ r) (d : p ⊣ s)
    {A₀ : E₀ ⥤ P₀} {A₁ : E₁ ⥤ P₁} (a : l ⋙ A₁ ≅ A₀ ⋙ p) (b : r ⋙ A₀ ⟶ A₁ ⋙ s) (G : E₀)
    (hu : A₀.map (e.unit.app G) ≫ b.app (l.obj G) ≫ s.map (a.hom.app G) =
      d.unit.app (A₀.obj G)) {K : E₁} (φ : l.obj G ⟶ K) :
    d.homEquiv _ _ (a.inv.app G ≫ A₁.map φ) = A₀.map (e.homEquiv G K φ) ≫ b.app K := by
  have hn := b.naturality φ
  simp only [Functor.comp_map] at hn
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← hu]
  simp [hn]

/-- The `homEquiv` of a restriction (`Adjunction.restrictFullyFaithful`) of an adjunction
`Adjunction.ofNatIsoLeft`, computed on the ambient categories. -/
theorem CategoryTheory.Adjunction.map_restrictFullyFaithful_ofNatIsoLeft_homEquiv
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {iC : C ⥤ C'} {iD : D ⥤ D'} {L₀ L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj : L₀ ⊣ R')
    (iso : L₀ ≅ L') (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful)
    {L : C ⥤ D} {R : D ⥤ C} (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC)
    {X : C} {Y : D} (φ : L.obj X ⟶ Y) :
    iC.map (((adj.ofNatIsoLeft iso).restrictFullyFaithful hiC hiD comm1 comm2).homEquiv X Y φ) =
      adj.homEquiv _ _ (iso.hom.app _ ≫ comm1.hom.app X ≫ iD.map φ) ≫ comm2.hom.app Y := by
  rw [Adjunction.restrictFullyFaithful_homEquiv_apply, Functor.FullyFaithful.map_preimage]
  simp [Adjunction.homEquiv_unit]

/-- **Comparison of exact functors and the single-degree embeddings.** For exact functors
`f₀ : C₀ ⥤ C₁`, `f₁ : P₀ ⥤ P₁`, `ν₀ : C₀ ⥤ P₀`, `ν₁ : C₁ ⥤ P₁` and `c : ν₀ ⋙ f₁ ≅ f₀ ⋙ ν₁`, the
isomorphism `D(f₀) ⋙ D(ν₁) ≅ D(ν₀) ⋙ D(f₁)` induced by `c` is, on an object placed in degree
zero, `c` placed in degree zero (modulo `Functor.mapDerivedCategorySingleFunctor`). -/
theorem CategoryTheory.Functor.mapDerivedCategorySingleFunctor_comparison
    {C₀ C₁ P₀ P₁ : Type*} [Category C₀] [Category C₁] [Category P₀] [Category P₁]
    [Abelian C₀] [Abelian C₁] [Abelian P₀] [Abelian P₁]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory P₀]
    [HasDerivedCategory P₁]
    (f₀ : C₀ ⥤ C₁) (f₁ : P₀ ⥤ P₁) (ν₀ : C₀ ⥤ P₀) (ν₁ : C₁ ⥤ P₁)
    [f₀.Additive] [PreservesFiniteLimits f₀] [PreservesFiniteColimits f₀]
    [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
    [ν₀.Additive] [PreservesFiniteLimits ν₀] [PreservesFiniteColimits ν₀]
    [ν₁.Additive] [PreservesFiniteLimits ν₁] [PreservesFiniteColimits ν₁]
    (c : ν₀ ⋙ f₁ ≅ f₀ ⋙ ν₁) (X : C₀) :
    f₁.mapDerivedCategory.map ((ν₀.mapDerivedCategorySingleFunctor 0).inv.app X) ≫
      ((mapDerivedCategoryCompIso f₀ ν₁).symm ≪≫ mapDerivedCategoryNatIso c.symm ≪≫
        mapDerivedCategoryCompIso ν₀ f₁).inv.app ((DerivedCategory.singleFunctor C₀ 0).obj X) ≫
      ν₁.mapDerivedCategory.map ((f₀.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (ν₁.mapDerivedCategorySingleFunctor 0).hom.app (f₀.obj X) =
    (f₁.mapDerivedCategorySingleFunctor 0).hom.app (ν₀.obj X) ≫
      (DerivedCategory.singleFunctor P₁ 0).map (c.hom.app X) := by
  have h₁ := mapDerivedCategoryNatIso_hom_app_singleFunctor c.symm X
  have h₂ := mapDerivedCategoryCompIso_hom_app_singleFunctor ν₀ f₁ X
  have h₁' : (mapDerivedCategoryNatIso c.symm).inv.app
        ((DerivedCategory.singleFunctor C₀ 0).obj X) ≫
        ((f₀ ⋙ ν₁).mapDerivedCategorySingleFunctor 0).hom.app X =
      ((ν₀ ⋙ f₁).mapDerivedCategorySingleFunctor 0).hom.app X ≫
        (DerivedCategory.singleFunctor P₁ 0).map (c.hom.app X) := by
    rw [← cancel_epi ((mapDerivedCategoryNatIso c.symm).hom.app _), Iso.hom_inv_id_app_assoc,
      reassoc_of% h₁]
    simp
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryCompIso_hom_app_singleFunctor, h₁', ← h₂]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc]
  simp

/-- The coherence behind the transport of `homEquiv` along the site comparison, in the setting of
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor_comparison`, with `κ : L₁ ≅ D(f₁)` any
isomorphism (in practice the identification of a left derived functor of the exact `f₁`). -/
theorem CategoryTheory.Functor.mapDerivedCategorySingleFunctor_comparison_comp
    {C₀ C₁ P₀ P₁ : Type*} [Category C₀] [Category C₁] [Category P₀] [Category P₁]
    [Abelian C₀] [Abelian C₁] [Abelian P₀] [Abelian P₁]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory P₀]
    [HasDerivedCategory P₁]
    (f₀ : C₀ ⥤ C₁) (f₁ : P₀ ⥤ P₁) (ν₀ : C₀ ⥤ P₀) (ν₁ : C₁ ⥤ P₁)
    [f₀.Additive] [PreservesFiniteLimits f₀] [PreservesFiniteColimits f₀]
    [f₁.Additive] [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
    [ν₀.Additive] [PreservesFiniteLimits ν₀] [PreservesFiniteColimits ν₀]
    [ν₁.Additive] [PreservesFiniteLimits ν₁] [PreservesFiniteColimits ν₁]
    (c : ν₀ ⋙ f₁ ≅ f₀ ⋙ ν₁) {L₁ : DerivedCategory P₀ ⥤ DerivedCategory P₁}
    (κ : L₁ ≅ f₁.mapDerivedCategory) (X : C₀) {W Z : DerivedCategory C₁}
    (j : f₀.mapDerivedCategory.obj ((DerivedCategory.singleFunctor C₀ 0).obj X) ≅ W)
    (χ : (DerivedCategory.singleFunctor C₁ 0).obj (f₀.obj X) ⟶ Z) {Y : DerivedCategory P₁}
    (γ : ν₁.mapDerivedCategory.obj Z ⟶ Y) :
    (κ.hom.app ((DerivedCategory.singleFunctor P₀ 0).obj (ν₀.obj X)) ≫
        (f₁.mapDerivedCategorySingleFunctor 0).hom.app (ν₀.obj X)) ≫
      (DerivedCategory.singleFunctor P₁ 0).map (c.hom.app X) ≫
      (ν₁.mapDerivedCategorySingleFunctor 0).inv.app (f₀.obj X) ≫
      ν₁.mapDerivedCategory.map χ ≫ γ =
    L₁.map ((ν₀.mapDerivedCategorySingleFunctor 0).inv.app X) ≫
      ((((κ.hom.app _ ≫
        ((mapDerivedCategoryCompIso f₀ ν₁).symm ≪≫ mapDerivedCategoryNatIso c.symm ≪≫
          mapDerivedCategoryCompIso ν₀ f₁).inv.app ((DerivedCategory.singleFunctor C₀ 0).obj X)) ≫
        ν₁.mapDerivedCategory.map j.hom) ≫
        ν₁.mapDerivedCategory.map (j.inv ≫ (f₀.mapDerivedCategorySingleFunctor 0).hom.app X ≫ χ)) ≫
        γ) := by
  have hc := mapDerivedCategorySingleFunctor_comparison f₀ f₁ ν₀ ν₁ c X
  simp only [Category.assoc, Functor.map_comp, Iso.map_hom_inv_id_assoc]
  rw [κ.hom.naturality_assoc, ← reassoc_of% hc, Iso.hom_inv_id_app_assoc]
  rfl

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The `homEquiv` of the bounded below étale derived adjunction `f^* ⊣ Rf_*`, computed by the
unbounded one. -/
theorem ι_map_derivedUpperStarLowerStarAdjunctionPlus_homEquiv {U V : Scheme.{u}} (f : U ⟶ V)
    (G : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (φ : (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.obj G ⟶ K) :
    DerivedCategory.Plus.ι.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).homEquiv G K φ) =
      (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctorIsoMapDerivedCategory.hom.app
              (DerivedCategory.Plus.ι.obj G) ≫
            (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlusCompatibility.inv.app
              G ≫
            DerivedCategory.Plus.ι.map φ) ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusCompatibility.inv.app K :=
  Adjunction.map_restrictFullyFaithful_ofNatIsoLeft_homEquiv
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctorIsoMapDerivedCategory
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlusCompatibility.symm
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusCompatibility.symm φ

/-- The inverse of `ProEtale.leftDerivedUpperStarComparisonIso`, unfolded. -/
theorem leftDerivedUpperStarComparisonIso_inv_app {U V : Scheme.{u}} (f : U ⟶ V)
    (G : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarComparisonIso f Λ).inv.app G =
      ((ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctorIsoMapDerivedCategory.hom.app
          ((DerivedCategory.Plus.ι ⋙
            (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory).obj G) ≫
        ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
          Functor.mapDerivedCategoryNatIso
            (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).symm ≪≫
          Functor.mapDerivedCategoryCompIso _ _).inv.app (DerivedCategory.Plus.ι.obj G)) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.map
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlusCompatibility.inv.app G) :=
  rfl

/-- **Transport of `homEquiv` of `f^* ⊣ Rf_*` along the site comparison**, for a sheaf `F` on
`V_ét` and a map `χ : (f^* F)[0] ⟶ X` to a bounded below complex: if the étale `homEquiv` of
`χ` is an isomorphism on `H^n`, so is the pro-étale `homEquiv` of `ν^* χ` (up to the canonical
identifications and an isomorphism `γ` on the target). -/
theorem isIso_homology_map_homEquiv_comparison_of_plus {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (X : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hX : DerivedCategory.TStructure.t.plus X)
    (χ : (DerivedCategory.singleFunctor _ 0).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F) ⟶ X)
    {Y : DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} Λ))}
    (γ : (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.obj X ≅ Y) (n : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _
        ((Etale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app F ≫
          χ)))) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _
        ((ProEtale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).obj F) ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app F) ≫
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategorySingleFunctor 0).inv.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.map χ ≫ γ.hom))) := by
  let G : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := ⟨X, hX⟩
  let φ : (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlus.obj G ⟶ K :=
    (ObjectProperty.fullyFaithfulι _).preimage
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlusCompatibility.hom.app G ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategorySingleFunctor 0).hom.app F ≫
          χ)
  have hφ : DerivedCategory.Plus.ι.map φ =
      (Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlusCompatibility.hom.app G ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategorySingleFunctor 0).hom.app F ≫
          χ :=
    (ObjectProperty.fullyFaithfulι _).map_preimage _
  have hψ : (ProEtale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).obj F) ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app F) ≫
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategorySingleFunctor 0).inv.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.map χ ≫ γ.hom =
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.map
          (((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategorySingleFunctor 0).inv.app
            F) ≫
        ((leftDerivedUpperStarComparisonIso f Λ).inv.app G ≫
          (DerivedCategory.Plus.ι ⋙
            (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory).map φ) ≫ γ.hom := by
    rw [leftDerivedUpperStarComparisonIso_inv_app, Functor.comp_map, hφ]
    exact Functor.mapDerivedCategorySingleFunctor_comparison_comp
      (Etale.upperStar (ModuleCat.{u + 1} Λ) f) (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f)
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) V) (comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f)
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctorIsoMapDerivedCategory F
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).mapDerivedCategoryPlusCompatibility.app G).symm
      χ γ.hom
  have h2 := Adjunction.homEquiv_inv_app_comp_map
    (A₀ := DerivedCategory.Plus.ι ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory)
    (A₁ := DerivedCategory.Plus.ι ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory)
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f)
    (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f)
    (leftDerivedUpperStarComparisonIso f Λ)
    (rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ)).hom G (comparison_unit Λ f G) φ
  have h3 : (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory).map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).homEquiv G K φ) =
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory.map
        ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _
          ((Etale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app F ≫
            χ) ≫
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusCompatibility.inv.app
            K) := by
    rw [Functor.comp_map, ι_map_derivedUpperStarLowerStarAdjunctionPlus_homEquiv, hφ,
      Iso.inv_hom_id_app_assoc]
    simp only [Etale.singleFunctorCompLeftDerivedUpperStarIso,
      Functor.singleFunctorCompLeftDerivedFunctorIso, Iso.trans_hom, NatTrans.comp_app,
      Category.assoc]
    rfl
  have heq : (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _
        ((ProEtale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).obj F) ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app F) ≫
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategorySingleFunctor 0).inv.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F) ≫
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.map χ ≫ γ.hom) =
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategorySingleFunctor 0).inv.app
          F ≫
        ((DerivedCategory.Plus.ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory).map
          ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).homEquiv G K φ) ≫
          (rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ)).hom.app K) ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.map γ.hom := by
    rw [hψ, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, ← h2]
    rfl
  have h1 : IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategory.map
        ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _
          ((Etale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app F ≫
            χ)))) :=
    (NatIso.isIso_map_iff
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryHomologyFunctorIso n)
      _).1 (by
        rw [Functor.comp_map]
        infer_instance)
  rw [heq, h3]
  simp only [Functor.map_comp]
  infer_instance

/-- The transport of `homEquiv` along the site comparison for a map of sheaves. -/
theorem isIso_homology_map_homEquiv_comparison {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (F₁ : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (φ : (Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F ⟶ F₁) (n : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _
        ((Etale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app F ≫
          (DerivedCategory.singleFunctor _ 0).map φ)))) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _
        ((ProEtale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app
            ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) V).obj F) ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app F ≫
              (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map φ)))) := by
  have hn := ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategorySingleFunctor
    0).hom.naturality φ
  simp only [Functor.comp_map] at hn
  rw [Functor.map_comp, ← Iso.inv_hom_id_app_assoc
    ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategorySingleFunctor 0)
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F)
    ((DerivedCategory.singleFunctor _ 0).map ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map φ)),
    ← hn]
  exact isIso_homology_map_homEquiv_comparison_of_plus Λ f F _ ⟨0, inferInstance⟩
    ((DerivedCategory.singleFunctor _ 0).map φ)
    (((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategorySingleFunctor 0).app F₁)
    n h

/-- The transport of `homEquiv` along the site comparison for a map of sheaves followed by an
extension class. -/
theorem isIso_homology_map_homEquiv_ext_comparison {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (F₁ F₂ : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (φ : (Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F ⟶ F₁) (x : Abelian.Ext F₁ F₂ 1)
    (n : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _
        ((Etale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app F ≫
          (DerivedCategory.singleFunctor _ 0).map φ ≫ x.hom)))) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _
        ((ProEtale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app
            ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) V).obj F) ≫
          (DerivedCategory.singleFunctor _ 0).map
            ((ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) f).hom.app F ≫
              (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map φ) ≫
          (x.mapExactFunctor (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) U)).hom))) := by
  have hn := ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategorySingleFunctor
    0).hom.naturality φ
  simp only [Functor.comp_map] at hn
  have key := isIso_homology_map_homEquiv_comparison_of_plus Λ f F _
    (DerivedCategory.TStructure.t.plus.le_shift ((1 : ℕ) : ℤ) _ ⟨0, inferInstance⟩)
    ((DerivedCategory.singleFunctor _ 0).map φ ≫ x.hom)
    (((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategory.commShiftIso
        ((1 : ℕ) : ℤ)).app _ ≪≫
      (shiftFunctor _ ((1 : ℕ) : ℤ)).mapIso
        (((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategorySingleFunctor 0).app
          F₂))
    n h
  rw [Abelian.Ext.mapExactFunctor_hom, ShiftedHom.map, Functor.map_comp, Category.assoc,
    ← Iso.inv_hom_id_app_assoc
      ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategorySingleFunctor 0)
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj F)
      ((DerivedCategory.singleFunctor _ 0).map
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).map φ) ≫ _),
    reassoc_of% hn.symm, Iso.hom_inv_id_app_assoc]
  simpa only [Functor.map_comp, Category.assoc, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.comp_obj] using key

/-- The vanishing of `H^n Rf_*` transported along the site comparison. -/
theorem isZero_homology_rightDerived_comparison {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f]
    (F₁ : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((Etale.rightDerivedLowerStar (ModuleCat.{u + 1} Λ) f).obj
        ((DerivedCategory.singleFunctor _ 0).obj F₁)))) :
    IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) U).obj F₁)))) := by
  let K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (DerivedCategory.Plus.singleFunctor _ 0).obj F₁
  refine IsZero.of_iso (Functor.map_isZero (comparisonUpperStar (ModuleCat.{u + 1} Λ) V) h)
    ((DerivedCategory.homologyFunctor _ n).mapIso
      ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctor.mapIso
        (((comparisonUpperStar (ModuleCat.{u + 1} Λ) U).mapDerivedCategorySingleFunctor 0).app
          F₁).symm) ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso
        ((rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ)).app K).symm ≪≫
      (((comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapDerivedCategoryHomologyFunctorIso
        n).app _).symm ≪≫
      (comparisonUpperStar (ModuleCat.{u + 1} Λ) V).mapIso
        ((DerivedCategory.homologyFunctor _ n).mapIso
          ((Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusCompatibility.app K)))

end AlgebraicGeometry.ProEtale

