/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Separators of Grothendieck abelian categories are presentable

Let `C` be a Grothendieck abelian category and `G` a separator of `C`. We show that `G` is
`κ`-presentable for any regular cardinal `κ` which is bigger than the cardinalities of
`Subobject G` and of `G ⟶ G`, and in particular for some regular cardinal `κ`.

This answers, for a separator, the expectation stated in the docstring of
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda`: there, the bijectivity of
`colim (Hom(G, Y j)) ⟶ Hom(G, colim Y)` is only shown for `κ`-filtered diagrams of
monomorphisms, while injectivity is shown in general
(`IsGrothendieckAbelian.IsPresentable.injectivity`).

## Proof of surjectivity

Let `R := (End G)ᵐᵒᵖ`, `U := preadditiveCoyonedaObj G : C ⥤ ModuleCat R` and let `T` be its
left adjoint `tensorObj G`. By the Gabriel-Popescu theorem, `U` is fully faithful and `T` is
exact. Let `Y : J ⥤ C` be a `κ`-filtered diagram with colimit `L` and let `f : G ⟶ L`.

* The comparison map `φ : colim (Y ⋙ U) ⟶ U L` is injective (by `injectivity`), and `T.map φ`
  is an isomorphism, because `T` preserves colimits and the counit `U ⋙ T ⟶ 𝟭` is an
  isomorphism.
* Let `g : R ⟶ U L` be the linear map `r ↦ r • f` and `P` the pullback of `φ` along `g`. Then
  `P ⟶ R` is injective, so `P` has cardinality `< κ` and is `κ`-presentable in `ModuleCat R`
  (`ModuleCat.isCardinalPresentable_of_hasCardinalLT`); and `T.map (P ⟶ R)` is an isomorphism,
  as `T` preserves pullbacks.
* By presentability, `P ⟶ colim (Y ⋙ U)` factors through some `U (Y j)`; since `T.map (P ⟶ R)`
  is an isomorphism, the adjunction extends the resulting map `P ⟶ U (Y j)` to `ψ : R ⟶ U (Y j)`,
  and shows that `g = ψ ≫ U.map (c.ι.app j)`. Evaluating at `1` gives `f = ψ 1 ≫ c.ι.app j`.

## Main results

- `IsGrothendieckAbelian.isCardinalPresentable_of_isSeparator`: a separator `G` is
  `κ`-presentable if `Subobject G` and `G ⟶ G` have cardinality `< κ`.
- `IsGrothendieckAbelian.exists_isCardinalPresentable_of_isSeparator`: a separator is
  `κ`-presentable for some regular cardinal `κ`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

namespace IsPresentable

set_option backward.isDefEq.respectTransparency false in
/-- If `G` is a separator of a Grothendieck abelian category and `κ` a regular cardinal
bigger than the cardinalities of `Subobject G` and `G ⟶ G`, then any morphism from `G`
to the colimit of a `κ`-filtered diagram factors through one of the objects of the diagram. -/
lemma surjectivity_of_isSeparator {G : C} (hG : IsSeparator G) {κ : Cardinal.{v}}
    [Fact κ.IsRegular] (h₁ : HasCardinalLT (Subobject G) κ) (h₂ : HasCardinalLT (G ⟶ G) κ)
    {J : Type v} [SmallCategory J] [IsCardinalFiltered J κ] {Y : J ⥤ C} {c : Cocone Y}
    (hc : IsColimit c) (f : G ⟶ c.pt) :
    ∃ (j : J) (y : G ⟶ Y.obj j), f = y ≫ c.ι.app j := by
  have := isFiltered_of_isCardinalFiltered J κ
  let U := preadditiveCoyonedaObj G
  let T := tensorObj G
  let adj : T ⊣ U := tensorObjPreadditiveCoyonedaObjAdjunction G
  have : U.Faithful := (isSeparator_iff_faithful_preadditiveCoyonedaObj G).1 hG
  have : U.Full := GabrielPopescu.full G hG
  have := GabrielPopescu.preservesFiniteLimits G hG
  have hR : HasCardinalLT (End G)ᵐᵒᵖ κ := h₂.of_injective _ MulOpposite.unop_injective
  -- the comparison map `colim (Y ⋙ U) ⟶ U c.pt`
  let φ : colimit (Y ⋙ U) ⟶ U.obj c.pt := colimit.desc _ (U.mapCocone c)
  have hφ (j : J) (y : G ⟶ Y.obj j) : φ (colimit.ι (Y ⋙ U) j y) = y ≫ c.ι.app j :=
    ConcreteCategory.congr_hom (colimit.ι_desc (U.mapCocone c) j) y
  have : Mono φ := by
    rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep (Y ⋙ U) x
    obtain ⟨k, a, ha⟩ := injectivity₀ hc h₁ y (by rw [← hφ]; exact hx)
    rw [← ConcreteCategory.congr_hom (colimit.w (Y ⋙ U) a) y]
    change colimit.ι (Y ⋙ U) k (y ≫ Y.map a) = 0
    rw [ha, map_zero]
  have : IsIso (T.map φ) := by
    have hT := isColimitOfPreserves T (colimit.isColimit (Y ⋙ U))
    have hc' := (IsColimit.precomposeHomEquiv
      (asIso (Functor.whiskerLeft Y adj.counit)) c).symm hc
    have : T.map φ ≫ adj.counit.app c.pt = (hT.coconePointUniqueUpToIso hc').hom :=
      hT.hom_ext fun j ↦ by
        rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
        dsimp [φ]
        rw [← T.map_comp_assoc, colimit.ι_desc]
        exact adj.counit.naturality (c.ι.app j)
    have : IsIso (T.map φ ≫ adj.counit.app c.pt) := by rw [this]; infer_instance
    exact IsIso.of_isIso_comp_right _ (adj.counit.app c.pt)
  -- the linear map `r ↦ r • f` and the pullback of `φ` along it
  let g : ModuleCat.of (End G)ᵐᵒᵖ (End G)ᵐᵒᵖ ⟶ U.obj c.pt :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ f)
  have hP := IsPullback.of_hasPullback φ g
  have : IsIso (T.map (pullback.snd φ g)) := (hP.map T).isIso_snd_of_isIso
  have : IsCardinalPresentable (pullback φ g) κ :=
    ModuleCat.isCardinalPresentable_of_hasCardinalLT _ κ hR
      (hR.of_injective _
        ((ModuleCat.mono_iff_injective (pullback.snd φ g)).1 inferInstance))
  obtain ⟨j, ψ₁, hψ₁⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ
    (colimit.isColimit (Y ⋙ U)) (pullback.fst φ g)
  -- extend `ψ₁` along `pullback.snd φ g`, using the adjunction
  let ψ : ModuleCat.of (End G)ᵐᵒᵖ (End G)ᵐᵒᵖ ⟶ U.obj (Y.obj j) :=
    adj.homEquiv _ _ (inv (T.map (pullback.snd φ g)) ≫ (adj.homEquiv _ _).symm ψ₁)
  have hψ : pullback.snd φ g ≫ ψ = ψ₁ := by
    rw [← adj.homEquiv_naturality_left, IsIso.hom_inv_id_assoc, Equiv.apply_symm_apply]
  have key : g = ψ ≫ U.map (c.ι.app j) := by
    apply (adj.homEquiv _ _).symm.injective
    rw [← cancel_epi (T.map (pullback.snd φ g)), ← adj.homEquiv_naturality_left_symm,
      ← adj.homEquiv_naturality_left_symm, reassoc_of% hψ, ← hP.w, ← hψ₁]
    dsimp only [φ, colimit.cocone_ι]
    rw [Category.assoc, colimit.ι_desc]
    rfl
  refine ⟨j, ψ 1, ?_⟩
  have : (1 : (End G)ᵐᵒᵖ) • f = ψ 1 ≫ c.ι.app j := ConcreteCategory.congr_hom key 1
  rwa [one_smul] at this

end IsPresentable

open IsPresentable in
/-- A separator `G` of a Grothendieck abelian category is `κ`-presentable for any regular
cardinal `κ` which is bigger than the cardinalities of `Subobject G` and of `G ⟶ G`. -/
theorem isCardinalPresentable_of_isSeparator {G : C} (hG : IsSeparator G)
    (κ : Cardinal.{v}) [Fact κ.IsRegular] (h₁ : HasCardinalLT (Subobject G) κ)
    (h₂ : HasCardinalLT (G ⟶ G) κ) : IsCardinalPresentable G κ where
  preservesColimitOfShape J _ _ := ⟨fun {Y} ↦ ⟨fun {c} hc ↦ ⟨by
    have := isFiltered_of_isCardinalFiltered J κ
    exact Types.FilteredColimit.isColimitOf' _ _
      (surjectivity_of_isSeparator hG h₁ h₂ hc) (injectivity hc h₁)⟩⟩⟩

/-- A separator `G` of a Grothendieck abelian category is `κ`-presentable for some regular
cardinal `κ`. -/
theorem exists_isCardinalPresentable_of_isSeparator {G : C} (hG : IsSeparator G) :
    ∃ (κ : Cardinal.{v}) (_ : Fact κ.IsRegular), IsCardinalPresentable G κ := by
  obtain ⟨κ, hκ, h⟩ := HasCardinalLT.exists_regular_cardinal.{v} (Subobject G ⊕ (G ⟶ G))
  have : Fact κ.IsRegular := ⟨hκ⟩
  exact ⟨κ, this, isCardinalPresentable_of_isSeparator hG κ
    (h.of_injective _ Sum.inl_injective) (h.of_injective _ Sum.inr_injective)⟩

end CategoryTheory.IsGrothendieckAbelian

