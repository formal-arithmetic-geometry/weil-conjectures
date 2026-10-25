/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-!

# Base change of Galois covers

The base change `P ×_Y Y' ⟶ Y'` of a finite étale Galois cover `P ⟶ Y` with group `G` along any
morphism `g : Y' ⟶ Y` is a finite étale Galois cover with group `G`
(`AlgebraicGeometry.Scheme.GaloisCover.pullback`). This is used to transport finite `ℓ`-group
monodromy along the covers of blueprint `det-tf-restriction-zero-covers`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.GaloisCover

variable {G : Type (u + 1)} [Group G] [Finite G] {Y Y' : Scheme.{u}} (c : GaloisCover G Y)
  (g : Y' ⟶ Y)

attribute [instance] isFinite etale surjective

/-- A version of `FinitaryPreExtensive.isIso_sigmaDesc_fst` for index types in any universe. -/
lemma isIso_sigmaDesc_fst {C : Type*} [Category C] [HasPullbacks C] [FinitaryPreExtensive C]
    {α : Type*}
    [Finite α] {X : C} {Z : α → C} (π : (a : α) → Z a ⟶ X) {W : C} (f : W ⟶ X)
    [HasCoproduct Z] [HasCoproduct (fun a ↦ pullback f (π a))]
    (hπ : IsIso (Sigma.desc π)) :
    IsIso (Sigma.desc ((fun _ ↦ pullback.fst _ _) : (a : α) → pullback f (π a) ⟶ _)) := by
  let c := (Cofan.mk _ ((fun _ ↦ pullback.fst _ _) : (a : α) → pullback f (π a) ⟶ _))
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  have hau : IsUniversalColimit (Cofan.mk X π) := FinitaryPreExtensive.isUniversal_finiteCoproducts
    ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mpr hπ).some
  refine hau.nonempty_isColimit_of_pullbackCone_left _ (𝟙 _) _ _ (fun i ↦ ?_)
    (PullbackCone.mk (𝟙 _) f (by simp)) (IsPullback.id_horiz f).isLimit _ (Iso.refl _)
    (by simp) (by simp [c]) (by simp [pullback.condition, c])
  exact pullback.isLimit _ _

/-- The action of `G` on the base change `P ×_Y Y'`. -/
noncomputable def pullbackSMul (γ : G) : pullback c.π g ⟶ pullback c.π g :=
  pullback.map c.π g c.π g (c.smul γ) (𝟙 Y') (𝟙 Y) (by simp [c.smul_π]) (by simp)

@[reassoc (attr := simp)]
lemma pullbackSMul_snd (γ : G) : c.pullbackSMul g γ ≫ pullback.snd c.π g = pullback.snd c.π g := by
  simp [pullbackSMul]

@[reassoc (attr := simp)]
lemma pullbackSMul_fst (γ : G) :
    c.pullbackSMul g γ ≫ pullback.fst c.π g = pullback.fst c.π g ≫ c.smul γ := by
  simp [pullbackSMul]

/-- The comparison map `P' ×_{Y'} P' ⟶ P ×_Y P`, `P' = P ×_Y Y'`. -/
noncomputable def pullbackPairMap :
    pullback (pullback.snd c.π g) (pullback.snd c.π g) ⟶ pullback c.π c.π :=
  pullback.map _ _ _ _ (pullback.fst c.π g) (pullback.fst c.π g) g pullback.condition.symm
    pullback.condition.symm

/-- The square `P' ×_{Y'} P' ⟶ P'` (second projection) over `P ×_Y P ⟶ P` is cartesian. -/
lemma isPullback_pullbackPairMap_snd :
    IsPullback (pullback.snd (pullback.snd c.π g) (pullback.snd c.π g)) (c.pullbackPairMap g)
      (pullback.fst c.π g) (pullback.snd c.π c.π) := by
  refine ⟨⟨by simp [pullbackPairMap]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ pullback.lift (pullback.lift (s.snd ≫ pullback.fst c.π c.π)
        (s.fst ≫ pullback.snd c.π g) ?_) s.fst ?_) ?_ ?_ ?_⟩⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, ← s.condition, Category.assoc,
      pullback.condition, Category.assoc]
  · simp
  · intro s
    simp
  · intro s
    apply pullback.hom_ext
    · simp [pullbackPairMap]
    · simp only [pullbackPairMap, Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd]
      exact s.condition
  · intro s m h₁ h₂
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simpa [pullbackPairMap] using congrArg (· ≫ pullback.fst c.π c.π) h₂
      · simp only [pullback.lift_fst, pullback.lift_snd, Category.assoc, ← h₁]
        rw [pullback.condition]
    · simpa using h₁

/-- For each `γ`, the square `(γ •, id) : P' ⟶ P' ×_{Y'} P'` over `(γ •, id) : P ⟶ P ×_Y P` is
cartesian. -/
lemma isPullback_lift_smul (γ : G) :
    IsPullback (pullback.lift (c.pullbackSMul g γ) (𝟙 _) (by simp))
      (pullback.fst c.π g) (c.pullbackPairMap g)
      (pullback.lift (c.smul γ) (𝟙 _) (by simp [c.smul_π])) := by
  refine IsPullback.of_right ?_ ?_ (c.isPullback_pullbackPairMap_snd g)
  · simpa using IsPullback.id_horiz (pullback.fst c.π g)
  · apply pullback.hom_ext <;> simp [pullbackPairMap]
    exact Category.id_comp _

/-- **Base change of a Galois cover**: for a finite étale Galois cover `P ⟶ Y` with group `G`
and any `g : Y' ⟶ Y`, the base change `P ×_Y Y' ⟶ Y'` is a finite étale Galois cover with
group `G`. -/
noncomputable def pullback : GaloisCover G Y' where
  P := Limits.pullback c.π g
  π := pullback.snd c.π g
  smul := c.pullbackSMul g
  smul_π γ := c.pullbackSMul_snd g γ
  one_smul := by
    apply pullback.hom_ext <;> simp [c.one_smul]
  mul_smul γ δ := by
    apply pullback.hom_ext <;> simp [c.mul_smul]
  isIso_sigmaDesc := by
    have := c.isIso_sigmaDesc
    have hfst := isIso_sigmaDesc_fst (fun γ : G ↦ pullback.lift (f := c.π) (g := c.π)
      (c.smul γ) (𝟙 c.P) (by simp [c.smul_π])) (c.pullbackPairMap g) this
    let e : ∀ γ : G, Limits.pullback c.π g ≅ Limits.pullback (c.pullbackPairMap g)
        (pullback.lift (f := c.π) (g := c.π) (c.smul γ) (𝟙 c.P) (by simp [c.smul_π])) :=
      fun γ ↦ (c.isPullback_lift_smul g γ).isoPullback
    have : Sigma.desc (fun γ : G ↦ pullback.lift (f := pullback.snd c.π g)
        (g := pullback.snd c.π g) (c.pullbackSMul g γ) (𝟙 _) (by simp)) =
        (Sigma.mapIso e).hom ≫ Sigma.desc (fun γ ↦ pullback.fst _ _) := by
      refine Sigma.hom_ext _ _ (fun γ ↦ ?_)
      simp [e, Sigma.mapIso]
    rw [this]
    infer_instance

end AlgebraicGeometry.Scheme.GaloisCover
