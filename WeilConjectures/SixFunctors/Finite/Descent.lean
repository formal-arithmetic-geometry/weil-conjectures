/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections
public import WeilConjectures.SixFunctors.Finite.Stalk

/-!
# Descent of sections along finite surjective morphisms

Let `r : Y' ⟶ Y` be finite and surjective and `G` an abelian étale sheaf on `Y`. A global
section `σ'` of `r^* G` whose two pullbacks to `Y' ×_Y Y'` agree descends to a global section
of `G`: the sequence `Γ(Y, G) ⟶ Γ(Y', r^* G) ⇉ Γ(Y' ×_Y Y', (r ∘ pr)^* G)` is an equalizer.
At a geometric point `ȳ` of `Y` with algebraically closed field, the stalk of `r_* r^* G` is
the product of copies of `G_ȳ` indexed by the geometric points of `Y'` over `ȳ`, and the two
maps to the stalk of the pushforward from `Y' ×_Y Y'` compare the components at the two
members of a pair of such points; since the fibre is nonempty, the equalizer is `G_ȳ`.

## References

- Stacks Project, Lemma 59.55.5, <https://stacks.math.columbia.edu/tag/09Z2>
- Stacks Project, Remark 59.55.6, <https://stacks.math.columbia.edu/tag/09Z3>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

open Scheme

section Helpers

variable {X : Scheme.{u}}

/-- The geometric point `u : Spec Ω ⟶ U` of an étale `X`-scheme `U` over the geometric point
`y` of `X`, as an element of the fibre of `pointSmallEtale y` at `U`. -/
noncomputable abbrev fiberPt {Ω : Type u} [Field Ω] [IsSepClosed Ω] {y : Spec (.of Ω) ⟶ X} {U : X.Etale}
    (u : Spec (.of Ω) ⟶ U.left) (hu : u ≫ U.hom = y) : (pointSmallEtale y).fiber.obj U :=
  CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk y) (V := (Etale.forget X).obj U) u hu

/-- Germs along equal geometric points `y = y'` at equal points `u₁ = u₁'`, `u₂ = u₂'` of
étale neighbourhoods agree as soon as they agree at `y`. -/
lemma toPresheafFiber_fiberPt_eq_of_eq {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {y y' : Spec (.of Ω) ⟶ X} (h : y = y') {U₁ U₂ : X.Etale}
    {u₁ u₁' : Spec (.of Ω) ⟶ U₁.left} {u₂ u₂' : Spec (.of Ω) ⟶ U₂.left}
    (e₁ : u₁ = u₁') (e₂ : u₂ = u₂') (hu₁ : u₁ ≫ U₁.hom = y) (hu₂ : u₂ ≫ U₂.hom = y)
    (hu₁' : u₁' ≫ U₁.hom = y') (hu₂' : u₂' ≫ U₂.hom = y')
    (F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (g₁ : F.obj (op U₁)) (g₂ : F.obj (op U₂))
    (H : (pointSmallEtale y).toPresheafFiber U₁ (fiberPt u₁ hu₁) F g₁ =
      (pointSmallEtale y).toPresheafFiber U₂ (fiberPt u₂ hu₂) F g₂) :
    (pointSmallEtale y').toPresheafFiber U₁ (fiberPt u₁' hu₁') F g₁ =
      (pointSmallEtale y').toPresheafFiber U₂ (fiberPt u₂' hu₂') F g₂ := by
  subst h e₁ e₂
  exact H

lemma fiberPt_congr {Ω : Type u} [Field Ω] [IsSepClosed Ω] {y : Spec (.of Ω) ⟶ X}
    {U : X.Etale} {u u' : Spec (.of Ω) ⟶ U.left} (e : u = u') (hu : u ≫ U.hom = y)
    (hu' : u' ≫ U.hom = y) : fiberPt u hu = fiberPt u' hu' := by
  subst e
  rfl

/-- The morphism from an étale `X`-scheme to the terminal étale `X`-scheme `X`. -/
noncomputable def toEtaleMkId (V : X.Etale) : V ⟶ Scheme.Etale.mk (𝟙 X) :=
  MorphismProperty.Over.homMk V.hom (Category.comp_id _)

@[simp]
lemma toEtaleMkId_left (V : X.Etale) : (toEtaleMkId V).left = V.hom :=
  rfl

/-- There is at most one morphism to the terminal étale `X`-scheme `X`. -/
lemma eq_toEtaleMkId {V : X.Etale} (a : V ⟶ Scheme.Etale.mk (𝟙 X)) : a = toEtaleMkId V := by
  apply MorphismProperty.Over.Hom.ext
  have ha : a.left ≫ 𝟙 X = V.hom := MorphismProperty.Over.w a
  exact (Category.comp_id a.left).symm.trans ha

lemma left_eq_hom_of_etaleMkId {V : X.Etale} (a : V ⟶ Scheme.Etale.mk (𝟙 X)) :
    a.left = V.hom := by
  rw [eq_toEtaleMkId a, toEtaleMkId_left]

end Helpers

section Germ

variable {R T : Scheme.{u}} (t : T ⟶ R) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- On stalks, the unit `G ⟶ t_* t^* G` followed by restriction to a geometric point `s` of `T`
and the identification `(t^* G)_s ≅ G_{s ≫ t}` is the identity. -/
lemma sheafFiber_map_unit_stalkRestrict_upperStarCompSheafFiberIso (s : Spec (.of Ω) ⟶ T) :
    (pointSmallEtale (s ≫ t)).sheafFiber.map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G) ≫
      Etale.stalkRestrict AddCommGrpCat.{u + 1} t (s ≫ t) ⟨s, rfl⟩
        ((t)^*[AddCommGrpCat.{u + 1}].obj G) ≫
      (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} t s).hom.app G = 𝟙 _ := by
  rw [Etale.stalkRestrict_eq_counit]
  have h := (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} t s).inv.naturality
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G)
  simp only [Category.assoc]
  rw [reassoc_of% h]
  rw [← Functor.map_comp_assoc, Adjunction.left_triangle_components, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_app]
  rfl

/-- The germ of `φ^* g` at a geometric point `v` of `V` is the germ of `g` at `v ≫ φ`, through
the identification `(t^* G)_s ≅ G_{s ≫ t}`. -/
lemma upperStarCompSheafFiberIso_hom_toPresheafFiber_pullSection (s : Spec (.of Ω) ⟶ T)
    {V : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left) (hφ : φ ≫ U.hom = V.hom ≫ t)
    (g : G.obj.obj (op U)) (v : (pointSmallEtale s).fiber.obj V) :
    (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} t s).hom.app G
      ((pointSmallEtale s).toPresheafFiber V v ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj
        (pullSection t G φ hφ g)) =
      (pointSmallEtale (s ≫ t)).toPresheafFiber U
        (fiberPt (v.left ≫ φ)
          (by
            have hv : v.left ≫ V.hom = s := CategoryTheory.Over.w v
            change (v.left ≫ φ) ≫ U.hom = s ≫ t
            rw [Category.assoc, hφ, reassoc_of% hv])) G.obj g := by
  set u : (pointSmallEtale (s ≫ t)).fiber.obj U := CategoryTheory.Over.homMk
    (U := CategoryTheory.Over.mk (s ≫ t)) (V := (Etale.forget R).obj U) (v.left ≫ φ) (by
      have hv : v.left ≫ V.hom = s := CategoryTheory.Over.w v
      change (v.left ≫ φ) ≫ U.hom = s ≫ t
      rw [Category.assoc, hφ, reassoc_of% hv])
  have hv : v.left ≫ V.hom = s := CategoryTheory.Over.w v
  have e : (pointSmallEtale s).fiber.map (homToPullback t φ hφ) v =
      ((Etale.baseChangeNbhd t (s ≫ t) ⟨s, rfl⟩).obj ⟨U, u⟩).2 := by
    refine CategoryTheory.Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
    · change (v.left ≫ (homToPullback t φ hφ).left) ≫ _ = _
      simp [u, Scheme.Hom.basePt]
    · change (v.left ≫ (homToPullback t φ hφ).left) ≫ _ = _
      simp [u, Scheme.Hom.basePt, hv]
  rw [pullSection, GrothendieckTopology.Point.toPresheafFiber_w_apply, e]
  have h1 := ConcreteCategory.congr_hom (Etale.toPresheafFiber_stalkRestrict AddCommGrpCat.{u + 1}
    t (s ≫ t) ⟨s, rfl⟩ ((t)^*[AddCommGrpCat.{u + 1}].obj G) ⟨U, u⟩)
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G).hom.app (op U) g)
  rw [ConcreteCategory.comp_apply] at h1
  erw [← h1]
  erw [← GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
  have h2 := ConcreteCategory.congr_hom
    (sheafFiber_map_unit_stalkRestrict_upperStarCompSheafFiberIso t G s)
    ((pointSmallEtale (s ≫ t)).toPresheafFiber U u G.obj g)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
  exact h2

end Germ

section Injective

variable {R T : Scheme.{u}} (t : T ⟶ R) (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- Pulling back sections along a surjective `φ : V ⟶ U` over `t` is injective: if `φ^* g`
vanishes, then so does `g`. -/
lemma eq_zero_of_pullSection_eq_zero {V : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) (hsurj : Function.Surjective φ) (g : G.obj.obj (op U))
    (h : pullSection t G φ hφ g = 0) : g = 0 := by
  choose x hx using hsurj
  choose V' a U' b φ' hφ' hxa hcomm hg using
    fun u : U.left ↦ exists_of_pullSection_eq_zero t G φ hφ g h (x u)
  refine eq_zero_of_forall_map_eq_zero G b (fun u ↦ ⟨u, ?_⟩) g hg
  obtain ⟨x', hx'⟩ := hxa u
  refine ⟨φ' u x', ?_⟩
  rw [← Scheme.Hom.comp_apply, hcomm u, Scheme.Hom.comp_apply, hx', hx]

end Injective

section Compare

variable {Y Y' : Scheme.{u}} (r : Y' ⟶ Y) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- If the two restrictions of a section `σ'` of `r^* G` to `Y' ×_Y Y'` agree, then any two
local presentations `σ'|_{V₁} = φ₁^* g₁` and `σ'|_{V₂} = φ₂^* g₂` have the same germs at
geometric points `v₁`, `v₂` of `V₁`, `V₂` over the same geometric point `y` of `Y`. -/
lemma toPresheafFiber_eq_of_restrictAlong_eq
    (σ' : ((r)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op (Scheme.Etale.mk (𝟙 Y'))))
    (h : restrictAlong r G (pullback.fst r r) (pullback.fst r r ≫ r) rfl
        (V := Scheme.Etale.mk (𝟙 Y'))
        (V' := Scheme.Etale.mk (𝟙 (pullback r r))) (pullback.fst r r)
        ((Category.comp_id _).trans (Category.id_comp _).symm) σ' =
      restrictAlong r G (pullback.snd r r) (pullback.fst r r ≫ r) pullback.condition
        (V := Scheme.Etale.mk (𝟙 Y'))
        (V' := Scheme.Etale.mk (𝟙 (pullback r r))) (pullback.snd r r)
        ((Category.comp_id _).trans (Category.id_comp _).symm) σ')
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ Y}
    {V₁ V₂ : Y'.Etale} (a₁ : V₁ ⟶ Scheme.Etale.mk (𝟙 Y')) (a₂ : V₂ ⟶ Scheme.Etale.mk (𝟙 Y'))
    {U₁ U₂ : Y.Etale} (φ₁ : V₁.left ⟶ U₁.left) (hφ₁ : φ₁ ≫ U₁.hom = V₁.hom ≫ r)
    (φ₂ : V₂.left ⟶ U₂.left) (hφ₂ : φ₂ ≫ U₂.hom = V₂.hom ≫ r)
    (g₁ : G.obj.obj (op U₁)) (g₂ : G.obj.obj (op U₂))
    (hrep₁ : ((r)^*[AddCommGrpCat.{u + 1}].obj G).obj.map a₁.op σ' = pullSection r G φ₁ hφ₁ g₁)
    (hrep₂ : ((r)^*[AddCommGrpCat.{u + 1}].obj G).obj.map a₂.op σ' = pullSection r G φ₂ hφ₂ g₂)
    (v₁ : Spec (.of Ω) ⟶ V₁.left) (v₂ : Spec (.of Ω) ⟶ V₂.left)
    (hv₁ : (v₁ ≫ φ₁) ≫ U₁.hom = y) (hv₂ : (v₂ ≫ φ₂) ≫ U₂.hom = y) :
    (pointSmallEtale y).toPresheafFiber U₁ (fiberPt (v₁ ≫ φ₁) hv₁) G.obj g₁ =
      (pointSmallEtale y).toPresheafFiber U₂ (fiberPt (v₂ ≫ φ₂) hv₂) G.obj g₂ := by
  have ha₁ := left_eq_hom_of_etaleMkId a₁
  have ha₂ := left_eq_hom_of_etaleMkId a₂
  have hy₁ : (v₁ ≫ V₁.hom) ≫ r = y := by
    rw [Category.assoc, ← hφ₁, ← Category.assoc, hv₁]
  have hy₂ : (v₂ ≫ V₂.hom) ≫ r = y := by
    rw [Category.assoc, ← hφ₂, ← Category.assoc, hv₂]
  let p : Spec (.of Ω) ⟶ pullback r r :=
    pullback.lift (v₁ ≫ V₁.hom) (v₂ ≫ V₂.hom) (hy₁.trans hy₂.symm)
  let W₁ := pullbackObj (V := Scheme.Etale.mk (𝟙 Y'))
    (V'' := Scheme.Etale.mk (𝟙 (pullback r r))) (pullback.fst r r) a₁
  let W := pullbackObj (V := Scheme.Etale.mk (𝟙 Y')) (V'' := W₁)
    (pullback.fst (pullback.fst r r) a₁.left ≫ pullback.snd r r) a₂
  let m₁ : W.left ⟶ V₁.left := pullback.fst _ _ ≫ pullback.snd _ _
  let m₂ : W.left ⟶ V₂.left := pullback.snd _ _
  have hW : W.hom = pullback.fst _ _ ≫ pullback.fst _ _ := by
    simp only [W, W₁, pullbackObj_hom]
    exact congrArg (_ ≫ ·) (Category.comp_id _)
  have hm₁ : m₁ ≫ V₁.hom = W.hom ≫ pullback.fst r r := by
    rw [hW, ← ha₁]
    simp [m₁, pullback.condition]
  have hm₂ : m₂ ≫ V₂.hom = W.hom ≫ pullback.snd r r := by
    rw [hW, ← ha₂]
    simp [m₂, ← pullback.condition]
  let c := toEtaleMkId W
  have e₁ : ((pullback.fst r r ≫ r)^*[AddCommGrpCat.{u + 1}].obj G).obj.map c.op
      (restrictAlong r G (pullback.fst r r) (pullback.fst r r ≫ r) rfl
        (V := Scheme.Etale.mk (𝟙 Y'))
        (V' := Scheme.Etale.mk (𝟙 (pullback r r))) (pullback.fst r r)
        ((Category.comp_id _).trans (Category.id_comp _).symm) σ') =
      pullSection (pullback.fst r r ≫ r) G (V := W) (m₁ ≫ φ₁)
        (by rw [Category.assoc, hφ₁, reassoc_of% hm₁]) g₁ := by
    rw [map_restrictAlong, restrictAlong_congr (h := show c.left ≫ pullback.fst r r =
      m₁ ≫ a₁.left by rw [ha₁, hm₁]; rfl),
      ← restrictAlong_map _ _ _ _ _ (V' := W) a₁ m₁ hm₁, hrep₁, restrictAlong_pullSection]
  have e₂ : ((pullback.fst r r ≫ r)^*[AddCommGrpCat.{u + 1}].obj G).obj.map c.op
      (restrictAlong r G (pullback.snd r r) (pullback.fst r r ≫ r) pullback.condition
        (V := Scheme.Etale.mk (𝟙 Y'))
        (V' := Scheme.Etale.mk (𝟙 (pullback r r))) (pullback.snd r r)
        ((Category.comp_id _).trans (Category.id_comp _).symm) σ') =
      pullSection (pullback.fst r r ≫ r) G (V := W) (m₂ ≫ φ₂)
        (by rw [Category.assoc, hφ₂, reassoc_of% hm₂, pullback.condition]) g₂ := by
    rw [map_restrictAlong, restrictAlong_congr (h := show c.left ≫ pullback.snd r r =
      m₂ ≫ a₂.left by rw [ha₂, hm₂]; rfl),
      ← restrictAlong_map _ _ _ _ _ (V' := W) a₂ m₂ hm₂, hrep₂, restrictAlong_pullSection]
  let w : Spec (.of Ω) ⟶ W.left :=
    pullback.lift (pullback.lift p v₁ (by simp [p, ha₁])) v₂ (by simp [p, ha₂])
  have hw : w ≫ W.hom = p := by
    simp [hW, w]
  have H := congrArg (fun z ↦ (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
    (pullback.fst r r ≫ r) p).hom.app G ((pointSmallEtale p).toPresheafFiber W (fiberPt w hw)
      ((pullback.fst r r ≫ r)^*[AddCommGrpCat.{u + 1}].obj G).obj z))
    (congrArg (((pullback.fst r r ≫ r)^*[AddCommGrpCat.{u + 1}].obj G).obj.map c.op) h)
  dsimp only at H
  rw [e₁, e₂, upperStarCompSheafFiberIso_hom_toPresheafFiber_pullSection,
    upperStarCompSheafFiberIso_hom_toPresheafFiber_pullSection] at H
  exact toPresheafFiber_fiberPt_eq_of_eq (by simp [p, hy₁]) (by simp [w, m₁])
    (by simp [w, m₂]) _ _ _ _ G.obj g₁ g₂ H

end Compare

/-- **Descent along a finite surjective morphism.** Let `r : Y' ⟶ Y` be finite and surjective,
`G` an abelian étale sheaf on `Y` and `σ'` a global section of `r^* G` (a section over the
terminal étale `Y'`-scheme `Y'`) whose two restrictions along the projections
`Y' ×_Y Y' ⟶ Y'` agree. Then `σ'` is the pullback of a global section of `G`. -/
@[stacks 09Z3]
theorem exists_pullSection_eq_of_isFinite_of_surjective {Y Y' : Scheme.{u}} (r : Y' ⟶ Y)
    [IsFinite r] [Surjective r] (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (σ' : ((r)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op (Scheme.Etale.mk (𝟙 Y'))))
    (h : restrictAlong r G (pullback.fst r r) (pullback.fst r r ≫ r) rfl
        (V := Scheme.Etale.mk (𝟙 Y'))
        (V' := Scheme.Etale.mk (𝟙 (pullback r r))) (pullback.fst r r)
        ((Category.comp_id _).trans (Category.id_comp _).symm) σ' =
      restrictAlong r G (pullback.snd r r) (pullback.fst r r ≫ r) pullback.condition
        (V := Scheme.Etale.mk (𝟙 Y'))
        (V' := Scheme.Etale.mk (𝟙 (pullback r r))) (pullback.snd r r)
        ((Category.comp_id _).trans (Category.id_comp _).symm) σ') :
    ∃ σ : G.obj.obj (op (Scheme.Etale.mk (𝟙 Y))),
      pullSection r G (V := Scheme.Etale.mk (𝟙 Y')) (U := Scheme.Etale.mk (𝟙 Y)) r
        ((Category.comp_id _).trans (Category.id_comp _).symm) σ = σ' :=
  sorry

end AlgebraicGeometry.Etale
