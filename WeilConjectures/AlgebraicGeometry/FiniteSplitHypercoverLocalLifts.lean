/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverEngine
public import WeilConjectures.AlgebraicGeometry.SplitEtaleHypercoverLocalCone

/-!
# Simplicial objects of the small étale site with local lifts

The construction `AlgebraicGeometry.FiniteSplitHypercoverEngine.exists_hypercover` refines a
simplicial object `Y` of `X_ét` whose boundaries lift étale locally. We show that this holds
for split étale hypercovers, for the constant simplicial object at the final object, and that
it is stable under degreewise products.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial CategoryTheory.SimplicialObject

namespace AlgebraicGeometry

namespace Scheme.Etale

variable {X : Scheme.{u}}

lemma ofArrows_unit_mem' {V T : X.Etale} (π : T ⟶ V) (hπ : Surjective π.left) :
    Sieve.ofArrows (fun _ : Unit ↦ T) (fun _ ↦ π) ∈ X.smallEtaleTopology V := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  simp only [Set.iUnion_const]
  exact Set.range_eq_univ.2 hπ.surj

/-- The constant simplicial object at the final object has local lifts. -/
lemma hasLocalLifts_const_terminal :
    HasLocalLifts ((Functor.const SimplexCategoryᵒᵖ).obj (⊤_ X.Etale)) := by
  intro m T p
  refine X.smallEtaleTopology.superset_covering (fun _ g _ ↦ ?_) (X.smallEtaleTopology.top_mem T)
  exact ⟨terminal.from _, BoundaryCone.ext' fun _ _ _ ↦ terminal.hom_ext _ _⟩

/-- The degreewise product of two simplicial objects of the small étale site. -/
@[simps]
def prodSimplicial (Y₁ Y₂ : SimplicialObject X.Etale) : SimplicialObject X.Etale where
  obj Δ := Y₁.obj Δ ⨯ Y₂.obj Δ
  map θ := prod.map (Y₁.map θ) (Y₂.map θ)
  map_id Δ := by ext <;> simp
  map_comp θ θ' := by ext <;> simp

/-- The first projection of `prodSimplicial`. -/
@[simps]
def prodSimplicialFst (Y₁ Y₂ : SimplicialObject X.Etale) : prodSimplicial Y₁ Y₂ ⟶ Y₁ where
  app _ := prod.fst

/-- The second projection of `prodSimplicial`. -/
@[simps]
def prodSimplicialSnd (Y₁ Y₂ : SimplicialObject X.Etale) : prodSimplicial Y₁ Y₂ ⟶ Y₂ where
  app _ := prod.snd

/-- The map to `prodSimplicial` given by two maps. -/
@[simps]
def prodSimplicialLift {W Y₁ Y₂ : SimplicialObject X.Etale} (f₁ : W ⟶ Y₁) (f₂ : W ⟶ Y₂) :
    W ⟶ prodSimplicial Y₁ Y₂ where
  app Δ := prod.lift (f₁.app Δ) (f₂.app Δ)
  naturality Δ Δ' θ := prod.hom_ext (by simp) (by simp)

lemma hasLocalLifts_prod {Y₁ Y₂ : SimplicialObject X.Etale} (h₁ : HasLocalLifts Y₁)
    (h₂ : HasLocalLifts Y₂) : HasLocalLifts (prodSimplicial Y₁ Y₂) := by
  intro m T p
  refine X.smallEtaleTopology.superset_covering ?_ (X.smallEtaleTopology.intersection_covering
    (h₁ m T (p.postcomp (prodSimplicialFst Y₁ Y₂)))
    (h₂ m T (p.postcomp (prodSimplicialSnd Y₁ Y₂))))
  rintro T' g ⟨⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩⟩
  refine ⟨prod.lift s₁ s₂, BoundaryCone.ext' fun Δ hΔ θ ↦ ?_⟩
  have e₁ := congrArg (fun c ↦ BoundaryCone.π c Δ hΔ θ) hs₁
  have e₂ := congrArg (fun c ↦ BoundaryCone.π c Δ hΔ θ) hs₂
  simp only [BoundaryCone.ofSimplex, BoundaryCone.precomp, BoundaryCone.postcomp,
    prodSimplicialFst_app, prodSimplicialSnd_app] at e₁ e₂
  apply prod.hom_ext
  · simp only [BoundaryCone.ofSimplex, BoundaryCone.precomp, prodSimplicial_map, Category.assoc,
      prod.map_fst, prod.lift_fst_assoc]
    rw [e₁]
  · simp only [BoundaryCone.ofSimplex, BoundaryCone.precomp, prodSimplicial_map, Category.assoc,
      prod.map_snd, prod.lift_snd_assoc]
    rw [e₂]

end Scheme.Etale

namespace SplitEtaleHypercover

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- A split étale hypercover has local lifts. -/
lemma hasLocalLifts (U : SplitEtaleHypercover X) : Scheme.Etale.HasLocalLifts U.simplicial := by
  intro m T p
  obtain ⟨T', π, s, hπ, hs⟩ := U.exists_cover_lift m p.π p.w
  refine X.smallEtaleTopology.superset_covering ?_ (Scheme.Etale.ofArrows_unit_mem' π hπ)
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨⟩
  exact ⟨s, BoundaryCone.ext' fun Δ hΔ θ ↦ hs Δ hΔ θ⟩

end SplitEtaleHypercover

end AlgebraicGeometry
