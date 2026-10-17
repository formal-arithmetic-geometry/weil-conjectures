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
        (⟨cT.π.app U.left, 𝟙 _, by rw [Category.comp_id, ← Category.assoc, cT.w U.hom, hg₀],
          by simp, by rw [hw₀, Category.id_comp]⟩ : LimitStage.Hom (varyingBaseStarStage w₀ j)
            (varyingBaseStage g w j U))).app ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))
      (fun {U V} φ ↦ (stalkHomology Λ q x).map ((LimitStage.transition Λ
        (⟨T.map φ.left, 𝟙 _, by rw [Category.comp_id, ← Category.assoc, ← T.map_comp, Over.w φ],
          by simp, by simpa using w.naturality φ.left⟩ :
          LimitStage.Hom (varyingBaseStage g w j U) (varyingBaseStage g w j V))).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) :=
  sorry

end AlgebraicGeometry.Etale
