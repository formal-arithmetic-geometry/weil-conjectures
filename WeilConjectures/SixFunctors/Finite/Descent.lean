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
        (CategoryTheory.Over.homMk (U := CategoryTheory.Over.mk (s ≫ t))
          (V := (Etale.forget R).obj U) (v.left ≫ φ)
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
