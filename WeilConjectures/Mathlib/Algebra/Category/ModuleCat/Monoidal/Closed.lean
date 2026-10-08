/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Enriched.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

/-!
# Enriched homs of functors to modules

Let `R` be a commutative ring and let `F₁ F₂ : J ⥤ ModuleCat R`. The category `ModuleCat R` is
enriched over itself through its internal hom, so `F₁` and `F₂` have an enriched hom
`enrichedHom (ModuleCat R) F₁ F₂`, an end of the modules of linear maps `F₁ j ⟶ F₂ j`. This file
identifies its elements with the natural transformations `F₁ ⟶ F₂`
(`ModuleCat.enrichedHomEquiv`), and deduces that reindexing along an equivalence of categories
`G : K ⥤ J` induces an isomorphism of enriched homs (`ModuleCat.isIso_precompEnrichedHom'`).

As a consequence, the functor enriched hom `functorEnrichedHom (ModuleCat R) P Q` of two
presheaves `P Q : Eᵒᵖ ⥤ ModuleCat R`, the internal hom of presheaves, commutes with restriction
along a functor `u : D ⥤ E` inducing equivalences `Under (op d) ≌ Under (op (u d))`
(`ModuleCat.functorEnrichedHomCompIso`). This applies to the forgetful functor from a slice
category, and is what makes the restriction of sheaves to a localization of a site commute with
internal homs.

## Main definitions and results

- `ModuleCat.enrichedHomApp`: the component at `j` of an element of the enriched hom.
- `ModuleCat.enrichedHomEquiv`: the elements of `enrichedHom (ModuleCat R) F₁ F₂` are the
  natural transformations `F₁ ⟶ F₂`.
- `ModuleCat.isIso_precompEnrichedHom'`: reindexing along an equivalence is an isomorphism of
  enriched homs.
- `ModuleCat.functorEnrichedHomCompIso`: `u.op ⋙ [P, Q] ≅ [u.op ⋙ P, u.op ⋙ Q]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory MonoidalClosed Enriched.FunctorCategory

namespace ModuleCat

variable {R : Type u} [CommRing R] {J : Type*} [Category* J]

section EnrichedHom

variable {F₁ F₂ : J ⥤ ModuleCat.{u} R} [HasEnrichedHom (ModuleCat.{u} R) F₁ F₂]

/-- The component at `j : J` of an element of the enriched hom of `F₁` and `F₂`: a linear map
`F₁ j ⟶ F₂ j`. -/
noncomputable abbrev enrichedHomApp (e : enrichedHom (ModuleCat.{u} R) F₁ F₂) (j : J) :
    F₁.obj j ⟶ F₂.obj j :=
  (enrichedHomπ (ModuleCat.{u} R) F₁ F₂ j).hom e

/-- The components of an element of the enriched hom are natural. -/
lemma enrichedHomApp_naturality (e : enrichedHom (ModuleCat.{u} R) F₁ F₂) {i j : J}
    (f : i ⟶ j) : F₁.map f ≫ enrichedHomApp e j = enrichedHomApp e i ≫ F₂.map f := by
  have := congr($(enrichedHom_condition (ModuleCat.{u} R) F₁ F₂ f).hom e)
  rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    enrichedOrdinaryCategorySelf_eHomWhiskerRight] at this
  exact this.symm

/-- Two elements of the enriched hom are equal if their components are. -/
lemma enrichedHom_ext {e e' : enrichedHom (ModuleCat.{u} R) F₁ F₂}
    (h : ∀ j, enrichedHomApp e j = enrichedHomApp e' j) : e = e' := by
  have := end_.hom_ext (f := ModuleCat.ofHom (LinearMap.toSpanSingleton R _ e))
    (g := ModuleCat.ofHom (LinearMap.toSpanSingleton R _ e')) fun j ↦ by
      ext1
      refine LinearMap.ext_ring ?_
      change enrichedHomApp ((1 : R) • e) j = enrichedHomApp ((1 : R) • e') j
      rw [one_smul, one_smul]
      exact h j
  simpa using congr(ModuleCat.Hom.hom $this (1 : R))

/-- The component at `j` of the element of the enriched hom corresponding to a natural
transformation `τ` is `τ.app j`. -/
lemma enrichedHomApp_homEquiv (τ : F₁ ⟶ F₂) (j : J) :
    enrichedHomApp ((Enriched.FunctorCategory.homEquiv (ModuleCat.{u} R) τ).hom (1 : R)) j =
      τ.app j := by
  have := congr($(homEquiv_apply_π (ModuleCat.{u} R) τ j).hom (1 : R))
  refine this.trans ?_
  change ((curry' (τ.app j)).hom (1 : R) : F₁.obj j ⟶ F₂.obj j) = τ.app j
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  change τ.app j ((ρ_ (F₁.obj j)).hom (x ⊗ₜ (1 : R))) = _
  rw [MonoidalCategory.rightUnitor_hom_apply, one_smul]

variable (F₁ F₂) in
/-- The elements of the enriched hom `enrichedHom (ModuleCat R) F₁ F₂` are the natural
transformations `F₁ ⟶ F₂`. -/
noncomputable def enrichedHomEquiv : enrichedHom (ModuleCat.{u} R) F₁ F₂ ≃ (F₁ ⟶ F₂) where
  toFun e :=
    { app := enrichedHomApp e
      naturality _ _ f := enrichedHomApp_naturality e f }
  invFun τ := (Enriched.FunctorCategory.homEquiv (ModuleCat.{u} R) τ).hom (1 : R)
  left_inv e := enrichedHom_ext fun j ↦ by
    rw [enrichedHomApp_homEquiv]
  right_inv τ := NatTrans.ext (funext fun j ↦ enrichedHomApp_homEquiv τ j)

@[simp]
lemma enrichedHomEquiv_apply_app (e : enrichedHom (ModuleCat.{u} R) F₁ F₂) (j : J) :
    (enrichedHomEquiv F₁ F₂ e).app j = enrichedHomApp e j :=
  rfl

@[simp]
lemma enrichedHomApp_enrichedHomEquiv_symm (τ : F₁ ⟶ F₂) (j : J) :
    enrichedHomApp ((enrichedHomEquiv F₁ F₂).symm τ) j = τ.app j :=
  enrichedHomApp_homEquiv τ j

end EnrichedHom

section Precomp

variable {K : Type*} [Category* K] (G : K ⥤ J) {F₁ F₂ : J ⥤ ModuleCat.{u} R}
  {F₁' F₂' : K ⥤ ModuleCat.{u} R} [HasEnrichedHom (ModuleCat.{u} R) F₁ F₂]
  [HasEnrichedHom (ModuleCat.{u} R) F₁' F₂']

/-- The components of the reindexing of an element of the enriched hom along `G`. -/
lemma enrichedHomApp_precompEnrichedHom' (e₁ : G ⋙ F₁ ≅ F₁') (e₂ : G ⋙ F₂ ≅ F₂')
    (e : enrichedHom (ModuleCat.{u} R) F₁ F₂) (k : K) :
    enrichedHomApp ((precompEnrichedHom' (ModuleCat.{u} R) G e₁ e₂).hom e) k =
      e₁.inv.app k ≫ enrichedHomApp e (G.obj k) ≫ e₂.hom.app k := by
  change (precompEnrichedHom' (ModuleCat.{u} R) G e₁ e₂ ≫
    enrichedHomπ (ModuleCat.{u} R) F₁' F₂' k).hom e = _
  rw [end_.lift_π, enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    enrichedOrdinaryCategorySelf_eHomWhiskerRight]
  rfl

/-- Under the identification of elements of enriched homs with natural transformations,
reindexing along `G` is whiskering by `G`. -/
lemma enrichedHomEquiv_precompEnrichedHom' (e₁ : G ⋙ F₁ ≅ F₁') (e₂ : G ⋙ F₂ ≅ F₂')
    (e : enrichedHom (ModuleCat.{u} R) F₁ F₂) :
    enrichedHomEquiv F₁' F₂' ((precompEnrichedHom' (ModuleCat.{u} R) G e₁ e₂).hom e) =
      e₁.inv ≫ Functor.whiskerLeft G (enrichedHomEquiv F₁ F₂ e) ≫ e₂.hom := by
  exact NatTrans.ext (funext fun k ↦ enrichedHomApp_precompEnrichedHom' G e₁ e₂ e k)

/-- Reindexing along an equivalence of categories `G : K ⥤ J` induces an isomorphism of
enriched homs: on elements it is whiskering of natural transformations by `G`. -/
lemma isIso_precompEnrichedHom' [G.IsEquivalence] (e₁ : G ⋙ F₁ ≅ F₁') (e₂ : G ⋙ F₂ ≅ F₂') :
    IsIso (precompEnrichedHom' (ModuleCat.{u} R) G e₁ e₂) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  have h : (precompEnrichedHom' (ModuleCat.{u} R) G e₁ e₂ : _ → _) =
      (enrichedHomEquiv F₁' F₂').symm ∘ (Iso.homCongr e₁ e₂) ∘
        ((Functor.whiskeringLeft K J _).obj G).map ∘ enrichedHomEquiv F₁ F₂ := by
    funext e
    apply (enrichedHomEquiv F₁' F₂').injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply, Iso.homCongr_apply,
      Functor.whiskeringLeft_obj_map]
    rw [← enrichedHomEquiv_precompEnrichedHom']
  rw [h]
  exact (enrichedHomEquiv F₁' F₂').symm.bijective.comp ((Iso.homCongr e₁ e₂).bijective.comp
    (((Functor.FullyFaithful.ofFullyFaithful _).map_bijective _ _).comp
      (enrichedHomEquiv F₁ F₂).bijective))

end Precomp

section Restriction

variable {D E : Type*} [Category* D] [Category* E] (u : D ⥤ E)
  (P Q : Eᵒᵖ ⥤ ModuleCat.{u} R) [HasFunctorEnrichedHom (ModuleCat.{u} R) P Q]
  [HasFunctorEnrichedHom (ModuleCat.{u} R) (u.op ⋙ P) (u.op ⋙ Q)]

/-- The component at `d` of `ModuleCat.functorEnrichedHomCompIso`: reindexing along
`Under (op d) ⥤ Under (op (u d))`. -/
noncomputable abbrev functorEnrichedHomCompApp (d : Dᵒᵖ) :
    (u.op ⋙ functorEnrichedHom (ModuleCat.{u} R) P Q).obj d ⟶
      (functorEnrichedHom (ModuleCat.{u} R) (u.op ⋙ P) (u.op ⋙ Q)).obj d :=
  precompEnrichedHom' (ModuleCat.{u} R) (Under.post (X := d) u.op)
    (F₁ := Under.forget _ ⋙ P) (F₂ := Under.forget _ ⋙ Q) (F₁' := Under.forget d ⋙ u.op ⋙ P)
    (F₂' := Under.forget d ⋙ u.op ⋙ Q) (Iso.refl _) (Iso.refl _)

lemma enrichedHomApp_functorEnrichedHomCompApp (d : Dᵒᵖ)
    (e : (functorEnrichedHom (ModuleCat.{u} R) P Q).obj (u.op.obj d)) (x : Under d) :
    enrichedHomApp ((functorEnrichedHomCompApp u P Q d).hom e) x =
      enrichedHomApp e ((Under.post u.op).obj x) := by
  refine (enrichedHomApp_precompEnrichedHom' (Under.post (X := d) u.op)
    (F₁ := Under.forget _ ⋙ P) (F₂ := Under.forget _ ⋙ Q) (F₁' := Under.forget d ⋙ u.op ⋙ P)
    (F₂' := Under.forget d ⋙ u.op ⋙ Q) (Iso.refl _) (Iso.refl _) e x).trans ?_
  exact (Category.id_comp _).trans (Category.comp_id _)


lemma functorEnrichedHomCompApp_naturality {d d' : Dᵒᵖ} (f : d ⟶ d') :
    (functorEnrichedHom (ModuleCat.{u} R) P Q).map (u.op.map f) ≫
        functorEnrichedHomCompApp u P Q d' =
      functorEnrichedHomCompApp u P Q d ≫
        (functorEnrichedHom (ModuleCat.{u} R) (u.op ⋙ P) (u.op ⋙ Q)).map f := by
  refine ModuleCat.hom_ext (LinearMap.ext fun e ↦ enrichedHom_ext fun x ↦ ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, functorEnrichedHom_map]
  have := enrichedHomApp_naturality (F₁ := Under.forget _ ⋙ P) (F₂ := Under.forget _ ⋙ Q) e
    (Under.homMk (𝟙 _) (by
      rw [Category.comp_id]
      change (u.map (f ≫ x.hom).unop).op = (u.map f.unop).op ≫ (u.map x.hom.unop).op
      rw [unop_comp, Functor.map_comp, op_comp]) :
      (Under.post u.op).obj ((Under.map f).obj x) ⟶
      (Under.map (u.op.map f)).obj ((Under.post u.op).obj x))
  simp only [Functor.comp_obj, Under.forget_obj, Functor.comp_map, Under.forget_map,
    Under.homMk_right, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id] at this
  refine ((enrichedHomApp_functorEnrichedHomCompApp u P Q d' _ x).trans ?_).trans
    (enrichedHomApp_precompEnrichedHom' (Under.map f) (F₁ := Under.forget d ⋙ u.op ⋙ P)
      (F₂ := Under.forget d ⋙ u.op ⋙ Q) (F₁' := Under.forget d' ⋙ u.op ⋙ P)
      (F₂' := Under.forget d' ⋙ u.op ⋙ Q) (Iso.refl _) (Iso.refl _) _ x).symm
  refine ((enrichedHomApp_precompEnrichedHom' (Under.map (u.op.map f))
    (F₁ := Under.forget _ ⋙ P) (F₂ := Under.forget _ ⋙ Q) (F₁' := Under.forget _ ⋙ P)
    (F₂' := Under.forget _ ⋙ Q) (Iso.refl _) (Iso.refl _) e _)).trans ?_
  have h2 := enrichedHomApp_functorEnrichedHomCompApp u P Q d e ((Under.map f).obj x)
  simp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  exact (Category.id_comp _).trans ((Category.comp_id _).trans ((this.trans h2.symm).trans
    ((Category.comp_id _).symm.trans (Category.id_comp _).symm)))

variable [∀ d : Dᵒᵖ, (Under.post (X := d) u.op).IsEquivalence]

instance (d : Dᵒᵖ) : IsIso (functorEnrichedHomCompApp u P Q d) :=
  isIso_precompEnrichedHom' _ _ _

/-- The restriction of the internal hom `[P, Q]` of presheaves along a functor `u : D ⥤ E`
inducing equivalences `Under (op d) ≌ Under (op (u d))` is the internal hom of the restrictions:
at `d`, the enriched hom of the restrictions of `P` and `Q` to `Under (op (u d))` is reindexed
along this equivalence. -/
noncomputable def functorEnrichedHomCompIso :
    u.op ⋙ functorEnrichedHom (ModuleCat.{u} R) P Q ≅
      functorEnrichedHom (ModuleCat.{u} R) (u.op ⋙ P) (u.op ⋙ Q) :=
  NatIso.ofComponents (fun d ↦ asIso (functorEnrichedHomCompApp u P Q d))
    (functorEnrichedHomCompApp_naturality u P Q)

@[simp]
lemma functorEnrichedHomCompIso_hom_app (d : Dᵒᵖ) :
    (functorEnrichedHomCompIso u P Q).hom.app d = functorEnrichedHomCompApp u P Q d :=
  rfl

end Restriction

end ModuleCat
