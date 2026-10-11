/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Conservative

/-!
# The essential image of the comparison pullback

Let `ν^* : Sh(X_ét, A) ⥤ Sh(X_proét, A)` be the comparison pullback, which is fully faithful.
A pro-étale sheaf `F` lies in its essential image if and only if the counit `ν^* ν_* F ⟶ F` is
an isomorphism. This file shows that this property is local for the étale topology and closed
under extensions.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_comparisonAdjunction_counit_app_localizationRestriction_iff`:
  for an étale `h : V ⟶ X`, the counit at the restriction `h^* F` is an isomorphism if and only if
  the restriction of the counit at `F` is.
- `AlgebraicGeometry.ProEtale.isIso_comparisonAdjunction_counit_app_of_cover`: the counit at `F`
  is an isomorphism as soon as the counits at the restrictions of `F` to the members of an
  étale family which is a pro-étale cover are.
- `AlgebraicGeometry.ProEtale.comparisonUpperStar_essImage_of_shortExact`: the essential image of
  `ν^*` is closed under extensions. This uses the full faithfulness of `ν^*` on bounded below
  derived categories.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Basic

variable {A}

/-- A morphism `ν^* G ⟶ F` to a sheaf of étale origin is an isomorphism as soon as its
restriction `ν_*` to the small étale site is: `ν^*` is fully faithful, with invertible unit. -/
lemma isIso_of_isIso_comparisonLowerStar_map {X : Scheme.{u}}
    {G : Sheaf X.smallEtaleTopology A} {F : Sheaf (ProEt.topology X) A}
    (φ : (ν^*(X)[A]).obj G ⟶ F) (hF : (ν^*(X)[A]).essImage F)
    (hφ : IsIso ((ν_*(X)[A]).map φ)) : IsIso φ := by
  obtain ⟨G', ⟨e⟩⟩ := hF
  have := isIso_comparisonAdjunction_unit A X
  obtain ⟨ψ, hψ⟩ := (ν^*(X)[A]).map_surjective (φ ≫ e.inv)
  have : IsIso ((ν_*(X)[A]).map ((ν^*(X)[A]).map ψ)) := by
    rw [hψ, Functor.map_comp]
    infer_instance
  have : IsIso ψ := by
    have h := (comparisonAdjunction A X).unit.naturality ψ
    rw [Functor.id_map] at h
    have : IsIso (ψ ≫ (comparisonAdjunction A X).unit.app G') := by
      rw [h, Functor.comp_map]
      infer_instance
    exact IsIso.of_isIso_comp_right ψ ((comparisonAdjunction A X).unit.app G')
  have : IsIso (φ ≫ e.inv) := by
    rw [← hψ]
    infer_instance
  exact IsIso.of_isIso_comp_right φ e.inv

/-- A pro-étale sheaf is of étale origin if and only if the counit of `ν^* ⊣ ν_*` at it is an
isomorphism. -/
lemma isIso_comparisonAdjunction_counit_app_iff {X : Scheme.{u}}
    (F : Sheaf (ProEt.topology X) A) :
    IsIso ((comparisonAdjunction A X).counit.app F) ↔ (ν^*(X)[A]).essImage F :=
  (comparisonAdjunction A X).isIso_counit_app_iff_mem_essImage

end Basic

section Restriction

variable {V X : Scheme.{u}} (h : V ⟶ X) [Etale h]

/-- The restrictions along an étale morphism `h : V ⟶ X` commute with the comparison
restriction `ν_*`: both composites are restriction along the inclusion `V_ét ⥤ X_proét`. -/
noncomputable def comparisonLowerStarLocalizationRestrictionIso :
    ν_*(X)[A] ⋙ Etale.localizationRestriction A h inferInstance ≅
      ProEtale.localizationRestriction A h inferInstance ⋙ ν_*(V)[A] :=
  Iso.refl _

/-- The comparison map `ν_V^* h^* ⟶ h^* ν_X^*` for an étale morphism `h : V ⟶ X`, the mate of
`AlgebraicGeometry.ProEtale.comparisonLowerStarLocalizationRestrictionIso`. It is an isomorphism
(`AlgebraicGeometry.ProEtale.isIso_comparisonUpperStarLocalizationRestrictionMap`). -/
noncomputable def comparisonUpperStarLocalizationRestrictionMap :
    Etale.localizationRestriction A h inferInstance ⋙ ν^*(V)[A] ⟶
      ν^*(X)[A] ⋙ ProEtale.localizationRestriction A h inferInstance :=
  (mateEquiv (comparisonAdjunction A X) (comparisonAdjunction A V)).symm
    (comparisonLowerStarLocalizationRestrictionIso A h).hom

/-- The counit of `ν^* ⊣ ν_*` at the restriction `h^* F` is the restriction of the counit at `F`,
up to the comparison map. -/
lemma comparisonAdjunction_counit_app_localizationRestriction
    (F : Sheaf (ProEt.topology X) A) :
    (comparisonAdjunction A V).counit.app
        ((ProEtale.localizationRestriction A h inferInstance).obj F) =
      (comparisonUpperStarLocalizationRestrictionMap A h).app ((ν_*(X)[A]).obj F) ≫
        (ProEtale.localizationRestriction A h inferInstance).map
          ((comparisonAdjunction A X).counit.app F) := by
  have := mateEquiv_counit_symm (comparisonAdjunction A X) (comparisonAdjunction A V)
    (TwoSquare.mk _ _ _ _ (comparisonLowerStarLocalizationRestrictionIso A h).hom) F
  exact ((Category.id_comp _).symm.trans
    (congrArg (· ≫ _) ((ν^*(V)[A]).map_id _).symm)).trans this

/-- The restriction of the comparison map to the small étale site of `V` is compatible with the
units of `ν^* ⊣ ν_*`. -/
lemma comparisonLowerStar_map_comparisonUpperStarLocalizationRestrictionMap_app
    (G : Sheaf X.smallEtaleTopology A) :
    (comparisonAdjunction A V).unit.app ((Etale.localizationRestriction A h inferInstance).obj G) ≫
      (ν_*(V)[A]).map ((comparisonUpperStarLocalizationRestrictionMap A h).app G) =
      (Etale.localizationRestriction A h inferInstance).map
        ((comparisonAdjunction A X).unit.app G) := by
  have := unit_mateEquiv_symm (comparisonAdjunction A X) (comparisonAdjunction A V)
    (TwoSquare.mk _ _ _ _ (comparisonLowerStarLocalizationRestrictionIso A h).hom) G
  exact this.symm.trans (Category.comp_id _)

/-- The restriction of `ν^* G` along an étale morphism is of étale origin. -/
lemma comparisonUpperStar_essImage_localizationRestriction_obj
    (G : Sheaf X.smallEtaleTopology A) :
    (ν^*(V)[A]).essImage ((ProEtale.localizationRestriction A h inferInstance).obj
      ((ν^*(X)[A]).obj G)) :=
  ⟨(Etale.upperStar A h).obj G, ⟨((comparisonUpperStarCompUpperStarIso A h).app G).symm ≪≫
    (ProEtale.upperStarIsoLocalizationRestriction A h inferInstance).app _⟩⟩

/-- The comparison map `ν_V^* h^* ⟶ h^* ν_X^*` along an étale morphism is an isomorphism: its
target is of étale origin, and its restriction to the small étale site of `V` is an isomorphism,
being compatible with the invertible units of `ν^* ⊣ ν_*`. -/
instance isIso_comparisonUpperStarLocalizationRestrictionMap_app
    (G : Sheaf X.smallEtaleTopology A) :
    IsIso ((comparisonUpperStarLocalizationRestrictionMap A h).app G) := by
  have := isIso_comparisonAdjunction_unit A X
  have := isIso_comparisonAdjunction_unit A V
  refine isIso_of_isIso_comparisonLowerStar_map _
    (comparisonUpperStar_essImage_localizationRestriction_obj A h G) ?_
  have : IsIso ((comparisonAdjunction A V).unit.app
      ((Etale.localizationRestriction A h inferInstance).obj G) ≫
      (ν_*(V)[A]).map ((comparisonUpperStarLocalizationRestrictionMap A h).app G)) := by
    rw [comparisonLowerStar_map_comparisonUpperStarLocalizationRestrictionMap_app]
    infer_instance
  exact IsIso.of_isIso_comp_left ((comparisonAdjunction A V).unit.app _) _

/-- For an étale `h : V ⟶ X`, the counit of `ν^* ⊣ ν_*` at the restriction `h^* F` is an
isomorphism if and only if the restriction of the counit at `F` is. -/
lemma isIso_comparisonAdjunction_counit_app_localizationRestriction_iff
    (F : Sheaf (ProEt.topology X) A) :
    IsIso ((comparisonAdjunction A V).counit.app
        ((ProEtale.localizationRestriction A h inferInstance).obj F)) ↔
      IsIso ((ProEtale.localizationRestriction A h inferInstance).map
        ((comparisonAdjunction A X).counit.app F)) := by
  rw [comparisonAdjunction_counit_app_localizationRestriction]
  exact isIso_comp_left_iff _ _

end Restriction

section Cover

variable {A}

/-- Being of étale origin is local for the étale topology: a pro-étale sheaf `F` on `X` is of
étale origin as soon as its pullbacks to the members of an étale family which is a pro-étale
covering family (for instance a Zariski open cover) are. -/
theorem comparisonUpperStar_essImage_of_cover {X : Scheme.{u}} {ι : Type*}
    {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X) [∀ i, Etale (g i)]
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (F : Sheaf (ProEt.topology X) A) (hF : ∀ i, (ν^*(W i)[A]).essImage ((g i)^*[A].obj F)) :
    (ν^*(X)[A]).essImage F := by
  rw [← isIso_comparisonAdjunction_counit_app_iff]
  refine ProEtale.isIso_of_isIso_localizationRestriction A _ g hg fun i ↦ ?_
  rw [← isIso_comparisonAdjunction_counit_app_localizationRestriction_iff,
    isIso_comparisonAdjunction_counit_app_iff]
  exact (ν^*(W i)[A]).essImage.prop_of_iso
    ((ProEtale.upperStarIsoLocalizationRestriction A (g i) inferInstance).app F) (hF i)

end Cover
section Extension

variable {A} [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The essential image of `ν^*` is closed under extensions: in a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of pro-étale sheaves with `F₁` and `F₃` of étale origin, `F₂` is of
étale origin. The extension class `F₃ ⟶ F₁[1]` in the derived category is the image under `ν^*`
of a morphism of étale complexes, by the full faithfulness of `ν^*` on bounded below derived
categories; `F₂` is `ν^*` of the degree `0` cohomology of its cone. -/
theorem comparisonUpperStar_essImage_of_shortExact {X : Scheme.{u}}
    {S : ShortComplex (Sheaf (ProEt.topology X) A)} (hS : S.ShortExact)
    (h₁ : (ν^*(X)[A]).essImage S.X₁) (h₃ : (ν^*(X)[A]).essImage S.X₃) :
    (ν^*(X)[A]).essImage S.X₂ := by
  obtain ⟨B, ⟨eB⟩⟩ := h₁
  obtain ⟨C, ⟨eC⟩⟩ := h₃
  let i₁ : (DerivedCategory.singleFunctor _ 0).obj S.X₁ ≅
      (ν^*(X)[A]).mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj B) :=
    (DerivedCategory.singleFunctor _ 0).mapIso eB.symm ≪≫
      ((ν^*(X)[A]).mapDerivedCategorySingleFunctor 0).symm.app B
  let i₃ : (DerivedCategory.singleFunctor _ 0).obj S.X₃ ≅
      (ν^*(X)[A]).mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj C) :=
    (DerivedCategory.singleFunctor _ 0).mapIso eC.symm ≪≫
      ((ν^*(X)[A]).mapDerivedCategorySingleFunctor 0).symm.app C
  have hB : DerivedCategory.TStructure.t.plus
      (((DerivedCategory.singleFunctor _ 0).obj B)⟦(1 : ℤ)⟧) :=
    DerivedCategory.TStructure.t.plus.le_shift 1 _ ⟨0, inferInstance⟩
  obtain ⟨δ, hδ⟩ := (bijective_comparisonUpperStar_mapDerivedCategory_map _ _ hB).2
    (i₃.inv ≫ hS.singleδ ≫ i₁.hom⟦(1 : ℤ)⟧' ≫
      ((ν^*(X)[A]).mapDerivedCategory.commShiftIso (1 : ℤ)).inv.app _)
  obtain ⟨M, f, g, hT⟩ := distinguished_cocone_triangle₂ δ
  have hT' := (ν^*(X)[A]).mapDerivedCategory.map_distinguished _ hT
  have hcomm : hS.singleδ ≫ i₁.hom⟦(1 : ℤ)⟧' = i₃.hom ≫ ((ν^*(X)[A]).mapDerivedCategory.map δ ≫
      ((ν^*(X)[A]).mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _) := by
    beta_reduce at hδ
    rw [hδ]
    simp
  obtain ⟨b, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism₂ _ _
    hS.singleTriangle_distinguished hT' i₁.hom i₃.hom hcomm
  have : IsIso b := isIso₂_of_isIso₁₃ (T := hS.singleTriangle)
    (T' := (ν^*(X)[A]).mapDerivedCategory.mapTriangle.obj (Triangle.mk f g δ))
    ⟨i₁.hom, b, i₃.hom, hb₁, hb₂, hcomm⟩ hS.singleTriangle_distinguished hT'
    (inferInstanceAs (IsIso i₁.hom)) (inferInstanceAs (IsIso i₃.hom))
  exact ⟨(DerivedCategory.homologyFunctor _ 0).obj M,
    ⟨(((ν^*(X)[A]).mapDerivedCategoryHomologyFunctorIso 0).app M ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso (asIso b).symm ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app S.X₂)⟩⟩

end Extension

end AlgebraicGeometry.ProEtale
