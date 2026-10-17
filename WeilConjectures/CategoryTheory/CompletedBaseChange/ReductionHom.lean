/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.CompletedBaseChange.Completed

/-!
# Morphisms of reductions of base change squares

A morphism `τ : ρ ⟶ ρ'` of reductions of base change squares
(`CategoryTheory.BaseChangeSquare.Reduction.Hom`) consists of natural transformations between the
four reduction functors, compatible with the comparisons `γ_f`, `γ_{f'}`, `δ_g`, `δ_{g'}`. For the
reductions `- ⊗ᴸ P_{n+1}` and `- ⊗ᴸ P_n` along a coefficient tower, the quotient
`q_n : P_{n+1} ⟶ P_n` gives such a morphism, and the induced maps of corners are the tower
transitions `a_{n+1,n}, b_{n+1,n}, c_{n+1,n}, d_{n+1,n}`.

## Main results

- `CategoryTheory.BaseChangeSquare.Reduction.Hom.arrows_comm`: the four arrows `h, v, h', v'`
  commute with the induced maps of corners (`lemma-weil-pbc-level-map-tower-compatibility`,
  abstract form).
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

namespace BaseChangeSquare

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒳' : Type u₃} {𝒴' : Type u₄}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒳'] [Category.{v₄} 𝒴']
  {𝒯 : Type u₅} {𝒰 : Type u₆} {𝒯' : Type u₇} {𝒰' : Type u₈}
  [Category.{v₅} 𝒯] [Category.{v₆} 𝒰] [Category.{v₇} 𝒯'] [Category.{v₈} 𝒰']

namespace Reduction

variable {𝔇 : BaseChangeSquare 𝒳 𝒴 𝒳' 𝒴'} {𝔗 : BaseChangeSquare 𝒯 𝒰 𝒯' 𝒰'}
  (ρ : Reduction 𝔇 𝔗)

/-- The components of the projection map `π_f`: the transpose of `γ_f` followed by the
counit. -/
@[reassoc]
lemma projF_app (K : 𝒳) :
    ρ.projF.natTrans.app K = 𝔗.adjF.unit.app (ρ.redY.obj (𝔇.lowerF.obj K)) ≫
      𝔗.lowerF.map (ρ.γF.natTrans.app (𝔇.lowerF.obj K) ≫ ρ.redX.map (𝔇.adjF.counit.app K)) := by
  simp [projF, mateEquiv_apply]

/-- The components of the projection map `π_{f'}`. -/
@[reassoc]
lemma projF'_app (K : 𝒳') :
    ρ.projF'.natTrans.app K = 𝔗.adjF'.unit.app (ρ.redY'.obj (𝔇.lowerF'.obj K)) ≫
      𝔗.lowerF'.map (ρ.γF'.natTrans.app (𝔇.lowerF'.obj K) ≫
        ρ.redX'.map (𝔇.adjF'.counit.app K)) := by
  simp [projF', mateEquiv_apply]

/-- A *morphism of reductions* `ρ ⟶ ρ'` of base change squares: natural transformations
`τ_Z : red_Z ⟶ red'_Z` on the four corners compatible with the comparisons `γ_f`, `γ_{f'}`,
`δ_g`, `δ_{g'}`. For the reductions modulo `P_{n+1}` and `P_n` these are the coefficient
quotients `q_n : P_{n+1} ⟶ P_n`. -/
structure Hom (ρ ρ' : Reduction 𝔇 𝔗) where
  /-- The map on `𝒳`. -/
  τX : ρ.redX ⟶ ρ'.redX
  /-- The map on `𝒴`. -/
  τY : ρ.redY ⟶ ρ'.redY
  /-- The map on `𝒳'`. -/
  τX' : ρ.redX' ⟶ ρ'.redX'
  /-- The map on `𝒴'`. -/
  τY' : ρ.redY' ⟶ ρ'.redY'
  commF (M : 𝒴) : 𝔗.upperF.map (τY.app M) ≫ ρ'.γF.natTrans.app M =
    ρ.γF.natTrans.app M ≫ τX.app (𝔇.upperF.obj M)
  commF' (M : 𝒴') : 𝔗.upperF'.map (τY'.app M) ≫ ρ'.γF'.natTrans.app M =
    ρ.γF'.natTrans.app M ≫ τX'.app (𝔇.upperF'.obj M)
  commG (M : 𝒴) : 𝔗.upperG.map (τY.app M) ≫ ρ'.δG.hom.app M =
    ρ.δG.hom.app M ≫ τY'.app (𝔇.upperG.obj M)
  commG' (K : 𝒳) : 𝔗.upperG'.map (τX.app K) ≫ ρ'.δG'.hom.app K =
    ρ.δG'.hom.app K ≫ τX'.app (𝔇.upperG'.obj K)

namespace Hom

variable {ρ} {ρ' : Reduction 𝔇 𝔗} (τ : Hom ρ ρ')

/-- The induced map `A ⟶ A'` on the corners `A = G^* red_Y f_* K`. -/
def mapA : ρ.cornerA ⟶ ρ'.cornerA := whiskerLeft 𝔇.lowerF (whiskerRight τ.τY 𝔗.upperG)

/-- The induced map `B ⟶ B'` on the corners `B = G^* F_* red_X K`. -/
def mapB : ρ.cornerB ⟶ ρ'.cornerB := whiskerRight τ.τX (𝔗.lowerF ⋙ 𝔗.upperG)

/-- The induced map `C ⟶ C'` on the corners `C = red_{Y'} f'_* g'^* K`. -/
def mapC : ρ.cornerC ⟶ ρ'.cornerC := whiskerLeft (𝔇.upperG' ⋙ 𝔇.lowerF') τ.τY'

/-- The induced map `D ⟶ D'` on the corners `D = F'_* G'^* red_X K`. -/
def mapD : ρ.cornerD ⟶ ρ'.cornerD := whiskerRight τ.τX (𝔗.upperG' ⋙ 𝔗.lowerF')

/-- The projection map `π_f` is natural with respect to morphisms of reductions. -/
@[reassoc]
lemma projF_naturality (K : 𝒳) :
    τ.τY.app (𝔇.lowerF.obj K) ≫ ρ'.projF.natTrans.app K =
      ρ.projF.natTrans.app K ≫ 𝔗.lowerF.map (τ.τX.app K) := by
  rw [projF_app, projF_app, ← 𝔗.adjF.unit_naturality_assoc, Category.assoc]
  simp only [Functor.comp_map, ← Functor.map_comp]
  congr 2
  rw [reassoc_of% (τ.commF (𝔇.lowerF.obj K)), Category.assoc]
  exact congrArg _ (τ.τX.naturality (𝔇.adjF.counit.app K)).symm

/-- The projection map `π_{f'}` is natural with respect to morphisms of reductions. -/
@[reassoc]
lemma projF'_naturality (K : 𝒳') :
    τ.τY'.app (𝔇.lowerF'.obj K) ≫ ρ'.projF'.natTrans.app K =
      ρ.projF'.natTrans.app K ≫ 𝔗.lowerF'.map (τ.τX'.app K) := by
  rw [projF'_app, projF'_app, ← 𝔗.adjF'.unit_naturality_assoc, Category.assoc]
  simp only [Functor.comp_map, ← Functor.map_comp]
  congr 2
  rw [reassoc_of% (τ.commF' (𝔇.lowerF'.obj K)), Category.assoc]
  exact congrArg _ (τ.τX'.naturality (𝔇.adjF'.counit.app K)).symm

/-- **The four arrows are maps of towers** (Blueprint
`lemma-weil-pbc-level-map-tower-compatibility`, abstract form): for a morphism of reductions
`τ : ρ ⟶ ρ'` (the coefficient quotient `P_{n+1} ⟶ P_n`), the induced corner maps
`a = mapA`, `b = mapB`, `c = mapC`, `d = mapD` satisfy
`b h = h a`, `c v = v a`, `d h' = h' c`, `d v' = v' b`. -/
lemma arrows_comm :
    ρ.arrowH ≫ τ.mapB = τ.mapA ≫ ρ'.arrowH ∧
    ρ.arrowV ≫ τ.mapC = τ.mapA ≫ ρ'.arrowV ∧
    ρ.arrowH' ≫ τ.mapD = τ.mapC ≫ ρ'.arrowH' ∧
    ρ.arrowV' ≫ τ.mapD = τ.mapB ≫ ρ'.arrowV' := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext K <;> simp only [NatTrans.comp_app]
  · rw [arrowH_app, arrowH_app]
    simp only [mapA, mapB, whiskerRight_app, whiskerLeft_app, Functor.comp_map,
      ← Functor.map_comp, projF_naturality]
  · rw [arrowV_app, arrowV_app]
    simp only [mapA, mapC, whiskerRight_app, whiskerLeft_app, Functor.comp_obj, Category.assoc]
    rw [← τ.τY'.naturality, reassoc_of% (τ.commG (𝔇.lowerF.obj K))]
  · rw [arrowH'_app, arrowH'_app]
    simp only [mapC, mapD, whiskerRight_app, whiskerLeft_app, Functor.comp_obj,
      Functor.comp_map, Category.assoc]
    rw [projF'_naturality_assoc, ← Functor.map_comp, ← Functor.map_comp]
    congr 2
    rw [Iso.inv_comp_eq, ← reassoc_of% (τ.commG' K), Iso.hom_inv_id, Category.comp_id]
  · simp only [arrowV'_app, mapB, mapD, whiskerRight_app, Functor.comp_map]
    exact (𝔗.exchange.natTrans.naturality (τ.τX.app K)).symm

end Hom

end Reduction

end BaseChangeSquare

end CategoryTheory
