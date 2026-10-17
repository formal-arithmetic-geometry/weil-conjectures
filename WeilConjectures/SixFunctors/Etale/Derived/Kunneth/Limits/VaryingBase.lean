/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.StageAlgebra
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Limits.PushforwardLimit

/-!
# Higher direct images along a limit with varying base

Let `gᵢ : Tᵢ ⟶ Sᵢ` be a cofiltered system of quasi-compact quasi-separated morphisms with affine
transition maps, with limit `g₀ : T ⟶ S`, the stages `Sᵢ` being quasi-compact and
quasi-separated, and let `G` be a sheaf on a scheme `W` to which the `Tᵢ` map compatibly. Then
on every geometric stalk of `S`, `R^q g₀_* (G|_T)` is the filtered colimit of the
`πᵢ^* R^q gᵢ_* (G|_{Tᵢ})` (`AlgebraicGeometry.Etale.isStalkColimit_varyingBaseSystem`,
Stacks 0EYM).

The proof combines the fixed-base statement `AlgebraicGeometry.Etale.higherDirectImage_limit`
(Stacks 09Z1) over each `Sⱼ`, for the system `Tₖ ⟶ Sₖ ⟶ Sⱼ`, with the statement
`AlgebraicGeometry.Etale.isStalkColimit_pushforwardStageSystem` for `g₀` and the system `Sⱼ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {I : Type u} [Category.{u} I] {S T : I ⥤ Scheme.{u}} (g : T ⟶ S) {cS : Cone S}
  {cT : Cone T} {g₀ : cT.pt ⟶ cS.pt} (hg₀ : ∀ i, g₀ ≫ cS.π.app i = cT.π.app i ≫ g.app i)
  {W : Scheme.{u}} (w : T ⟶ (Functor.const I).obj W) (w₀ : cT.pt ⟶ W)
  (hw₀ : ∀ i, cT.π.app i ≫ w.app i = w₀)

/-- The system of stages `(Tᵢ, Sᵢ, gᵢ, πᵢ, wᵢ)` over `S = cS.pt`, with limit stage
`(T, S, g₀, 𝟙, w₀)`. -/
@[simps]
noncomputable def varyingBaseSystem : LimitStageSystem cS.pt W I where
  obj i := ⟨T.obj i, S.obj i, g.app i, cS.π.app i, w.app i⟩
  map f := ⟨T.map f, S.map f, g.naturality f, cS.w f, by simpa using w.naturality f⟩
  map_id i := LimitStage.Hom.ext (T.map_id i) (S.map_id i)
  map_comp f g := LimitStage.Hom.ext (T.map_comp f g) (S.map_comp f g)
  pt := ⟨cT.pt, cS.pt, g₀, 𝟙 _, w₀⟩
  π i := ⟨cT.π.app i, cS.π.app i, (hg₀ i).symm, by simp, hw₀ i⟩
  w f := LimitStage.Hom.ext (cT.w f) (cS.w f)

/-- The stage `(Tₖ, Sⱼ, Tₖ ⟶ Tⱼ ⟶ Sⱼ, πⱼ, wₖ)` attached to `U = (k ⟶ j)`. -/
@[simps]
def varyingBaseStage (j : I) (U : Over j) : LimitStage cS.pt W :=
  ⟨T.obj U.left, S.obj j, T.map U.hom ≫ g.app j, cS.π.app j, w.app U.left⟩

/-- The stage `(T, Sⱼ, g₀ ≫ πⱼ, πⱼ, 𝟙 ≫ w₀)`. -/
@[simps]
def varyingBaseStarStage (j : I) : LimitStage cS.pt W :=
  ⟨cT.pt, S.obj j, g₀ ≫ cS.π.app j, cS.π.app j, 𝟙 _ ≫ w₀⟩

/-- The morphism of stages from `(T, Sⱼ, …)` to `(Tₖ, Sⱼ, …)` for `U = (k ⟶ j)`. -/
abbrev varyingBaseStarHom (j : I) (U : Over j) :
    LimitStage.Hom (varyingBaseStarStage (cS := cS) w₀ j) (varyingBaseStage g w j U) :=
  ⟨cT.π.app U.left, 𝟙 _, by rw [Category.comp_id, ← Category.assoc, cT.w U.hom, hg₀],
    by simp, by rw [hw₀, Category.id_comp]⟩

/-- The morphism of stages from `(Tₖ, Sⱼ, …)` to `(Tₗ, Sⱼ, …)` for a morphism `U ⟶ V` over
`j`. -/
abbrev varyingBaseStageHom {j : I} {U V : Over j} (φ : U ⟶ V) :
    LimitStage.Hom (varyingBaseStage (cS := cS) g w j U) (varyingBaseStage g w j V) :=
  ⟨T.map φ.left, 𝟙 _, by rw [Category.comp_id, ← Category.assoc, ← T.map_comp, Over.w φ],
    by simp, by simpa using w.naturality φ.left⟩

include hg₀ hw₀ in
/-- **The fixed-base input.** Over `Sⱼ`, `R^q (T ⟶ Sⱼ)_* (G|_T)` is the filtered colimit of the
`R^q (Tₖ ⟶ Sⱼ)_* (G|_{Tₖ})`, `k ⟶ j`, pulled back to `S` (Stacks 09Z1). -/
lemma isElementwiseColimit_varyingBaseStage [IsCofiltered I] (hT : IsLimit cT)
    [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (S.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (T.map f)] [QuasiCompact g₀] [QuasiSeparated g₀]
    (j : I) (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (x : cS.pt) :
    ModuleCat.IsElementwiseColimit
      (fun U : Over j ↦ (stalkHomology Λ q x).obj
        ((LimitStage.functor Λ (varyingBaseStage g w j U)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))
      ((stalkHomology Λ q x).obj ((LimitStage.functor Λ (varyingBaseStarStage w₀ j)).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))
      (fun U ↦ (stalkHomology Λ q x).map ((LimitStage.transition Λ
        (varyingBaseStarHom g hg₀ w w₀ hw₀ j U)).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))
      (fun {_ _} φ ↦ (stalkHomology Λ q x).map ((LimitStage.transition Λ
        (varyingBaseStageHom g w φ)).app ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) :=
  sorry

/-- The `[*]`-system `(T, Sⱼ, g₀ ≫ πⱼ, πⱼ, 𝟙 ≫ w₀)`. -/
noncomputable abbrev varyingBaseStarSystem : LimitStageSystem cS.pt W I :=
  (pushforwardStageSystem cS g₀).mapW w₀

lemma isStalkColimit_varyingBaseStarSystem [IsCofiltered I] (hS : IsLimit cS)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (S.map f)]
    [∀ i, CompactSpace (S.obj i)] [∀ i, QuasiSeparatedSpace (S.obj i)]
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (varyingBaseStarSystem (g₀ := g₀) w₀).IsStalkColimit Λ
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G) q :=
  LimitStageSystem.isStalkColimit_mapW w₀ _ (LimitStageSystem.isStalkColimit_of_iso _
    ((((w₀)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app G)
    (isStalkColimit_pushforwardStageSystem Λ cS g₀ hS _ q))

include hg₀ hw₀ in
/-- **Higher direct images along a limit with varying base** (Stacks 0EYM), on geometric
stalks: `R^q g₀_* (G|_T)` is the filtered colimit of the `πᵢ^* R^q gᵢ_* (G|_{Tᵢ})`. -/
theorem isStalkColimit_varyingBaseSystem [IsCofiltered I] (hS : IsLimit cS) (hT : IsLimit cT)
    [∀ i, QuasiCompact (g.app i)] [∀ i, QuasiSeparated (g.app i)]
    [∀ i, CompactSpace (S.obj i)] [∀ i, QuasiSeparatedSpace (S.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (S.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (T.map f)] [QuasiCompact g₀] [QuasiSeparated g₀]
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    (varyingBaseSystem g hg₀ w w₀ hw₀).IsStalkColimit Λ
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G) q := by
  intro x
  have hE := isStalkColimit_varyingBaseStarSystem Λ (g₀ := g₀) w₀ hS G q x
  have hD := fun j ↦ isElementwiseColimit_varyingBaseStage Λ g hg₀ w w₀ hw₀ hT j G q x
  let K := (DerivedCategory.Plus.singleFunctor (Sheaf W.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0).obj G
  let 𝒜 := varyingBaseSystem g hg₀ w w₀ hw₀
  let ℰ := varyingBaseStarSystem (g₀ := g₀) w₀
  have tc := LimitStage.transition_apply_comp Λ q x K
  let ζ : LimitStage.Hom ℰ.pt 𝒜.pt := ⟨𝟙 _, 𝟙 _, by simp [ℰ, 𝒜], by simp [ℰ, 𝒜], by simp [ℰ, 𝒜]⟩
  let ζ' : LimitStage.Hom 𝒜.pt ℰ.pt := ⟨𝟙 _, 𝟙 _, by simp [ℰ, 𝒜], by simp [ℰ, 𝒜], by simp [ℰ, 𝒜]⟩
  let ρ (k : I) : LimitStage.Hom (varyingBaseStage g w k (Over.mk (𝟙 k))) (𝒜.obj k) :=
    ⟨𝟙 _, 𝟙 _, by simp [𝒜], by simp [𝒜], by simp [𝒜]⟩
  let ψ {j : I} (U : Over j) : LimitStage.Hom (𝒜.obj U.left) (varyingBaseStage g w j U) :=
    ⟨𝟙 _, S.map U.hom, by simp [𝒜], by simp [𝒜], by simp [𝒜]⟩
  let θ {α β : LimitStage cS.pt W} (φ : LimitStage.Hom α β) :=
    ((stalkHomology Λ q x).map ((LimitStage.transition Λ φ).app K)).hom
  have tc' {α β γ : LimitStage cS.pt W} (φ : LimitStage.Hom α β) (ψ : LimitStage.Hom β γ) (y) :
      θ φ (θ ψ y) = θ (φ.comp ψ) y := tc φ ψ _ rfl y
  let σD (j : I) (U : Over j) := varyingBaseStarHom g hg₀ w w₀ hw₀ j U
  refine ⟨fun b ↦ ?_, fun k a ha ↦ ?_⟩
  · obtain ⟨j, e, he⟩ := hE.1 (θ ζ b)
    obtain ⟨U, d, rfl⟩ := (hD j).1 e
    refine ⟨U.left, θ (ψ U) d, ?_⟩
    have hχ : (𝒜.π U.left).comp (ψ U) = ζ'.comp ((ℰ.π j).comp (σD j U)) :=
      LimitStage.Hom.ext (by simp [ζ', ψ, σD, 𝒜, ℰ]) (by simp [ζ', ψ, σD, 𝒜, ℰ])
    have hinv := LimitStage.transition_apply_inv Λ q x K ζ' ζ
      (LimitStage.Hom.ext (by simp [ζ, ζ']) (by simp [ζ, ζ'])) b
    change θ (𝒜.π U.left) (θ (ψ U) d) = b
    rw [tc', hχ, ← tc', ← tc']
    exact (congrArg (θ ζ') he).trans hinv
  · let e := θ (σD k (Over.mk (𝟙 k))) (θ (ρ k) a)
    have he0 : θ (ℰ.π k) e = 0 := by
      have hχ : (ℰ.π k).comp ((σD k (Over.mk (𝟙 k))).comp (ρ k)) = ζ.comp (𝒜.π k) :=
        LimitStage.Hom.ext (by simp [ζ, ρ, σD, 𝒜, ℰ]) (by simp [ζ, ρ, σD, 𝒜, ℰ])
      have : θ (𝒜.π k) a = 0 := ha
      simp only [e]
      rw [tc', tc', hχ, ← tc', this, map_zero]
    obtain ⟨j, f, hf⟩ := hE.2 k e he0
    let aj := θ (𝒜.map f) a
    have hd0 : θ (σD j (Over.mk (𝟙 j))) (θ (ρ j) aj) = 0 := by
      have hχ : ((σD j (Over.mk (𝟙 j))).comp (ρ j)).comp (𝒜.map f) =
          (ℰ.map f).comp ((σD k (Over.mk (𝟙 k))).comp (ρ k)) :=
        LimitStage.Hom.ext (by simp [ρ, σD, 𝒜, ℰ]) (by simp [ρ, σD, 𝒜, ℰ])
      have : θ (ℰ.map f) e = 0 := hf
      simp only [aj]
      rw [tc', tc', hχ, ← tc', ← tc']
      exact this
    obtain ⟨V, φ, hφ⟩ := (hD j).2 (Over.mk (𝟙 j)) (θ (ρ j) aj) hd0
    refine ⟨V.left, V.hom ≫ f, ?_⟩
    have hχ : 𝒜.map (V.hom ≫ f) = (((ψ V).comp (varyingBaseStageHom g w φ)).comp (ρ j)).comp
        (𝒜.map f) :=
      LimitStage.Hom.ext (by simp [ψ, ρ, 𝒜, ← Over.w φ]) (by simp [ψ, ρ, 𝒜])
    have hφ' : θ (varyingBaseStageHom g w φ) (θ (ρ j) aj) = 0 := hφ
    change θ (𝒜.map (V.hom ≫ f)) a = 0
    rw [hχ, ← tc', ← tc', ← tc']
    simp only [aj] at hφ'
    rw [hφ', map_zero]

end AlgebraicGeometry.Etale
