/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.TransitionComp

/-!
# Stages of a base-change problem

Fix a Cartesian square `Y --e--> T`, `Y --h--> X` over `g : T ⟶ S` and `p : X ⟶ S`. A *stage*
over a morphism `π : T' ⟶ T` (`AlgebraicGeometry.Etale.BaseChangeStage`) is a Cartesian square
`Y' --e'--> T'`, `Y' --h'--> X` over `π ≫ g` and `p`, together with the map `a : Y' ⟶ Y`
covering `π`. For `K ∈ D⁺(T_ét)` it comes with the transition map
`Rh_*(e^* K) ⟶ Rh'_*(e'^* π^* K)` (`AlgebraicGeometry.Etale.BaseChangeStage.transition`), the
transition map of `AlgebraicGeometry.Etale.lowerStarPlusTransition` followed by the
composition isomorphisms of the derived pullbacks along `a ≫ e = e' ≫ π`.

Stages compose (`AlgebraicGeometry.Etale.BaseChangeStage.comp`): a stage over `π₂ : T₂ ⟶ T₁`
relative to a stage over `π₁ : T₁ ⟶ T` gives a stage over `π₂ ≫ π₁`, and the transition maps
satisfy the cocycle condition
(`AlgebraicGeometry.Etale.BaseChangeStage.transition_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X S T Y : Scheme.{u}}

variable (p : X ⟶ S) (g : T ⟶ S) (e : Y ⟶ T) (h : Y ⟶ X) in
/-- A stage of the base-change problem of the square `Y --e--> T`, `Y --h--> X` over a morphism
`π : T' ⟶ T`: a Cartesian square `Y' --e'--> T'`, `Y' --h'--> X` over `g' = π ≫ g` and `p`,
and a map `a : Y' ⟶ Y` over `π` and over `X`. -/
structure Etale.BaseChangeStage {T' : Scheme.{u}} (π : T' ⟶ T) where
  /-- the total space of the stage -/
  Y' : Scheme.{u}
  /-- the projection to `T'` -/
  e' : Y' ⟶ T'
  /-- the projection to `X` -/
  h' : Y' ⟶ X
  /-- the structure morphism of `T'` over `S` -/
  g' : T' ⟶ S
  /-- the map to `Y` -/
  a : Y' ⟶ Y
  isPullback : IsPullback e' h' g' p
  wg : π ≫ g = g'
  wa : a ≫ e = e' ≫ π
  wh : a ≫ h = h'

namespace Etale.BaseChangeStage

variable {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X} {T₁ T₂ : Scheme.{u}}

/-- The transition map `Rh_*(e^* K) ⟶ Rh'_*(e'^* π^* K)` of a stage. -/
noncomputable def transition {π : T₁ ⟶ T} (s : Etale.BaseChangeStage p g e h π)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    R+((h)_*[ModuleCat.{u + 1} Λ]).obj (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ⟶
      R+((s.h')_*[ModuleCat.{u + 1} Λ]).obj
        (D+((s.e')^*[ModuleCat.{u + 1} Λ]).obj (D+((π)^*[ModuleCat.{u + 1} Λ]).obj K)) :=
  Etale.lowerStarPlusTransition Λ s.a h s.h' s.wh (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
    R+((s.h')_*[ModuleCat.{u + 1} Λ]).map
      ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) s.a e (s.a ≫ e) rfl).inv.app K ≫
        (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) s.e' π (s.a ≫ e) s.wa).hom.app K)

/-- The composite of a stage `s₁` over `π₁ : T₁ ⟶ T` and a stage `s₂` over `π₂ : T₂ ⟶ T₁`
relative to `s₁`: a stage over `π₂ ≫ π₁`. -/
@[simps]
def comp {π₁ : T₁ ⟶ T} (s₁ : Etale.BaseChangeStage p g e h π₁) {π₂ : T₂ ⟶ T₁}
    (s₂ : Etale.BaseChangeStage p s₁.g' s₁.e' s₁.h' π₂) :
    Etale.BaseChangeStage p g e h (π₂ ≫ π₁) where
  Y' := s₂.Y'
  e' := s₂.e'
  h' := s₂.h'
  g' := s₂.g'
  a := s₂.a ≫ s₁.a
  isPullback := s₂.isPullback
  wg := by rw [Category.assoc, s₁.wg, s₂.wg]
  wa := by rw [Category.assoc, s₁.wa, reassoc_of% s₂.wa]
  wh := by rw [Category.assoc, s₁.wh, s₂.wh]

/-- The composition isomorphisms of the derived pullbacks satisfy the coherence needed for the
cocycle condition of the transition maps. -/
private lemma comp_coherence {Y₁ Y₂ : Scheme.{u}} {π₁ : T₁ ⟶ T} {π₂ : T₂ ⟶ T₁}
    (a₁ : Y₁ ⟶ Y) (a₂ : Y₂ ⟶ Y₁) (e₁ : Y₁ ⟶ T₁) (e₂ : Y₂ ⟶ T₂) (wa₁ : a₁ ≫ e = e₁ ≫ π₁)
    (wa₂ : a₂ ≫ e₁ = e₂ ≫ π₂) (wa₁₂ : (a₂ ≫ a₁) ≫ e = e₂ ≫ π₂ ≫ π₁)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ a₁ (a₂ ≫ a₁) rfl).hom.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      D+((a₂)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₁ e (a₁ ≫ e) rfl).inv.app K ≫
          (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₁ π₁ (a₁ ≫ e) wa₁).hom.app K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a₂ e₁ (a₂ ≫ e₁) rfl).inv.app
        (D+((π₁)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₂ π₂ (a₂ ≫ e₁) wa₂).hom.app
        (D+((π₁)^*[ModuleCat.{u + 1} Λ]).obj K) =
    ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (a₂ ≫ a₁) e ((a₂ ≫ a₁) ≫ e)
        rfl).inv.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e₂ (π₂ ≫ π₁) ((a₂ ≫ a₁) ≫ e)
        wa₁₂).hom.app K) ≫
      D+((e₂)^*[ModuleCat.{u + 1} Λ]).map
        ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) π₂ π₁ (π₂ ≫ π₁) rfl).hom.app K) := by
  -- `(a₂ ≫ a₁) ≫ e = a₂ ≫ (a₁ ≫ e)`
  have h₁ := Etale.upperStarCompDerivedPlus_assoc_app (ModuleCat.{u + 1} Λ) a₂ a₁ e (a₂ ≫ a₁)
    (a₁ ≫ e) ((a₂ ≫ a₁) ≫ e) rfl rfl rfl (Category.assoc _ _ _) K
  -- `(a₂ ≫ a₁) ≫ e = a₂ ≫ (e₁ ≫ π₁)`
  have h₂ := Etale.upperStarCompDerivedPlus_assoc_app (ModuleCat.{u + 1} Λ) a₂ e₁ π₁ (a₂ ≫ e₁)
    (a₁ ≫ e) ((a₂ ≫ a₁) ≫ e) rfl wa₁ (by rw [Category.assoc, wa₁, ← Category.assoc])
    (Category.assoc _ _ _) K
  -- `(a₂ ≫ a₁) ≫ e = e₂ ≫ (π₂ ≫ π₁)`
  have h₃ := Etale.upperStarCompDerivedPlus_assoc_app (ModuleCat.{u + 1} Λ) e₂ π₂ π₁ (a₂ ≫ e₁)
    (π₂ ≫ π₁) ((a₂ ≫ a₁) ≫ e) wa₂ rfl
    (by rw [Category.assoc, wa₁, ← Category.assoc]) wa₁₂ K
  rw [← cancel_epi ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) (a₂ ≫ a₁) e
    ((a₂ ≫ a₁) ≫ e) rfl).hom.app K)]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  rw [← reassoc_of% h₁, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% h₂, Iso.hom_inv_id_app_assoc, ← h₃]

/-- **The cocycle condition for the transition maps of stages.** The transition map of the
composite stage `s₁.comp s₂`, followed by the composition isomorphism
`(π₂ ≫ π₁)^* ≅ π₁^* ⋙ π₂^*`, is the transition map of `s₁` followed by the one of `s₂`. -/
lemma transition_comp {π₁ : T₁ ⟶ T} (s₁ : Etale.BaseChangeStage p g e h π₁) {π₂ : T₂ ⟶ T₁}
    (s₂ : Etale.BaseChangeStage p s₁.g' s₁.e' s₁.h' π₂)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (s₁.comp s₂).transition Λ K ≫
        R+((s₂.h')_*[ModuleCat.{u + 1} Λ]).map (D+((s₂.e')^*[ModuleCat.{u + 1} Λ]).map
          ((Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) π₂ π₁ (π₂ ≫ π₁) rfl).hom.app
            K)) =
      s₁.transition Λ K ≫ s₂.transition Λ (D+((π₁)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  dsimp only [transition, comp]
  simp only [Category.assoc]
  rw [Etale.lowerStarPlusTransition_naturality_assoc,
    ← Etale.lowerStarPlusTransition_comp_assoc Λ s₁.a s₂.a (s₂.a ≫ s₁.a) rfl h s₁.h' s₂.h' s₁.wh
      s₂.wh (by rw [Category.assoc, s₁.wh, s₂.wh])]
  refine (Category.assoc _ _ _).trans ?_
  congr 1
  have hc := congrArg (R+((s₂.h')_*[ModuleCat.{u + 1} Λ])).map (comp_coherence Λ s₁.a s₂.a s₁.e'
    s₂.e' s₁.wa s₂.wa (by rw [Category.assoc, s₁.wa, reassoc_of% s₂.wa]) K).symm
  simp only [Functor.map_comp, Category.assoc] at hc ⊢
  exact (Category.assoc _ _ _).trans hc

/-- The transition map of a stage is compatible with the derived base-change maps: the
base-change map of the base square followed by the transition map is the pullback of the
transition map `Rg_* K ⟶ Rg'_*(π^* K)` followed by the base-change map of the stage. -/
lemma baseChange_app_comp_transition (bsq : CommSq e h g p) {π : T₁ ⟶ T}
    (s : Etale.BaseChangeStage p g e h π)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (Etale.baseChange (ModuleCat.{u + 1} Λ) bsq).app K ≫ s.transition Λ K =
      D+((p)^*[ModuleCat.{u + 1} Λ]).map (Etale.lowerStarPlusTransition Λ π g s.g' s.wg K) ≫
        (Etale.baseChange (ModuleCat.{u + 1} Λ) s.isPullback.toCommSq).app
          (D+((π)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  obtain ⟨Y', e', h', g', a, hpb, wg, wa, wh⟩ := s
  subst wg
  have h₀ := Etale.baseChange_app_comp_lowerStarPlusTransition Λ bsq π hpb.toCommSq a wa wh K
  have key : (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) a e (a ≫ e) rfl).inv.app K ≫
      (Etale.upperStarCompDerivedPlus (ModuleCat.{u + 1} Λ) e' π (a ≫ e) wa).hom.app K =
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app K ≫ eqToHom (by rw [wa]) ≫
        (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e' π).hom.app K := by
    rw [Etale.upperStarCompDerivedPlus_eq_eqToIso_trans (ModuleCat.{u + 1} Λ) e' π (a ≫ e) wa,
      Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app]
    rfl
  dsimp only [transition]
  rw [key]
  exact h₀

/-- The transition map of a stage along a universal homeomorphism `a` (for instance an
isomorphism, or the base change of a thickening) is an isomorphism. -/
lemma isIso_transition {π : T₁ ⟶ T} (s : Etale.BaseChangeStage p g e h π)
    [IsUniversalHomeomorphism s.a]
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (s.transition Λ K) := by
  have := Etale.isIso_lowerStarPlusTransition Λ s.a h s.h' s.wh
    (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K)
  rw [transition]
  infer_instance

/-- A stage over `π` is a stage over any `π'` equal to `π`. -/
@[simps]
def congr {π π' : T₁ ⟶ T} (hπ : π = π') (s : Etale.BaseChangeStage p g e h π) :
    Etale.BaseChangeStage p g e h π' where
  Y' := s.Y'
  e' := s.e'
  h' := s.h'
  g' := s.g'
  a := s.a
  isPullback := s.isPullback
  wg := hπ ▸ s.wg
  wa := hπ ▸ s.wa
  wh := s.wh

/-- A stage with the map `a` replaced by an equal one. -/
@[simps]
def copyA {π : T₁ ⟶ T} (s : Etale.BaseChangeStage p g e h π) (a : s.Y' ⟶ Y) (ha : a = s.a) :
    Etale.BaseChangeStage p g e h π where
  Y' := s.Y'
  e' := s.e'
  h' := s.h'
  g' := s.g'
  a := a
  isPullback := s.isPullback
  wg := s.wg
  wa := ha ▸ s.wa
  wh := ha ▸ s.wh

lemma copyA_eq {π : T₁ ⟶ T} (s : Etale.BaseChangeStage p g e h π) (a : s.Y' ⟶ Y)
    (ha : a = s.a) : s.copyA a ha = s := by
  subst ha
  rfl

/-- The canonical stage over `π`, built from the chosen pullback of `p` along `π ≫ g`. -/
@[simps]
noncomputable def canonical (bsq : IsPullback e h g p) (π : T₁ ⟶ T) :
    Etale.BaseChangeStage p g e h π where
  Y' := pullback (π ≫ g) p
  e' := pullback.fst (π ≫ g) p
  h' := pullback.snd (π ≫ g) p
  g' := π ≫ g
  a := bsq.lift (pullback.fst (π ≫ g) p ≫ π) (pullback.snd (π ≫ g) p)
    (by rw [Category.assoc]; exact pullback.condition)
  isPullback := IsPullback.of_hasPullback (π ≫ g) p
  wg := rfl
  wa := bsq.lift_fst _ _ _
  wh := bsq.lift_snd _ _ _

/-- The comparison stage over `𝟙 T₁` between two stages `s` and `s'` over the same `π`, relative
to `s`: the identification of the total space of `s'` with the one of `s`. -/
@[simps]
noncomputable def comparison {π : T₁ ⟶ T} (s s' : Etale.BaseChangeStage p g e h π) :
    Etale.BaseChangeStage p s.g' s.e' s.h' (𝟙 T₁) where
  Y' := s'.Y'
  e' := s'.e'
  h' := s'.h'
  g' := s'.g'
  a := s.isPullback.lift s'.e' s'.h' (by rw [← s.wg, s'.wg]; exact s'.isPullback.w)
  isPullback := s'.isPullback
  wg := by rw [Category.id_comp, ← s.wg, s'.wg]
  wa := by rw [IsPullback.lift_fst, Category.comp_id]
  wh := IsPullback.lift_snd _ _ _ _

instance {π : T₁ ⟶ T} (s s' : Etale.BaseChangeStage p g e h π) :
    IsIso (s.comparison s').a := by
  dsimp only [comparison]
  refine ⟨s'.isPullback.lift s.e' s.h' (by rw [← s'.wg, s.wg]; exact s.isPullback.w), ?_, ?_⟩
  · apply s'.isPullback.hom_ext <;> simp
  · apply s.isPullback.hom_ext <;> simp

end Etale.BaseChangeStage

end AlgebraicGeometry
