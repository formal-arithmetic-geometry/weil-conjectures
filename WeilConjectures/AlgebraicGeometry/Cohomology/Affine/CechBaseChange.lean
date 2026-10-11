/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections
public import WeilConjectures.Topology.Sheaves.CechCriterion

/-!
# Čech complexes of invertible modules under affine base change

Consider a cartesian square of schemes
```
Y --g--> X
|        |
iY       iX
v        v
T --f--> S
```
with `T` affine, and an affine open `V ⊆ S` containing the image of `T`; write `A = Γ(S, V)` and
`B = Γ(T, ⊤)`. For an `𝒪_X`-module `ℱ` and an affine open `W ⊆ iX⁻¹ V` on which `ℱ` has a free
generator, the map `B ⊗[A] Γ(ℱ, W) ⟶ Γ(g^* ℱ, g⁻¹ W)`, `b ⊗ x ↦ iY^♯ b • g^* x`, is bijective
(`AlgebraicGeometry.Scheme.Modules.sectionsBaseChange_bijective`): this is the base change of the
ring of functions of the affine `W`.

Consequently, for a finite cover `U` of `iX⁻¹ V` by such opens, all of whose finite intersections
are affine, the Čech complex of `g^* ℱ` for the cover `g⁻¹ U` of `Y` is the base change
`B ⊗[A] Č(U, ℱ)` of the Čech complex of `ℱ`
(`AlgebraicGeometry.Scheme.Modules.cechBaseChange_bijective`,
`AlgebraicGeometry.Scheme.Modules.cechBaseChange_d`).

The `A`-module structures on the sections of `ℱ` are not instances: the statements take them as
instance arguments together with the hypothesis that they are restriction of scalars along
`iX^♯ : Γ(S, V) ⟶ Γ(X, W)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y S T : Scheme.{u}} {g : Y ⟶ X} {iY : Y ⟶ T} {iX : X ⟶ S} {f : T ⟶ S}

section Sections

variable (w : g ≫ iX = iY ≫ f) {V : S.Opens} (hfV : ⊤ ≤ f ⁻¹ᵁ V) (ℱ : X.Modules)
  {W : X.Opens} (hWV : W ≤ iX ⁻¹ᵁ V)
  [Algebra Γ(S, V) Γ(T, ⊤)] (hf : algebraMap Γ(S, V) Γ(T, ⊤) = (f.appLE V ⊤ hfV).hom)
  [Module Γ(S, V) Γ(ℱ, W)] (hW : ∀ (a : Γ(S, V)) (x : Γ(ℱ, W)), a • x = iX.appLE V W hWV a • x)

omit [Algebra Γ(S, V) Γ(T, ⊤)] in
include w in
lemma appLE_comp_eq_app_appLE (a : Γ(S, V)) :
    iY.appLE ⊤ (g ⁻¹ᵁ W) (le_top.trans iY.preimage_top.ge) (f.appLE V ⊤ hfV a) = g.app W (iX.appLE V W hWV a) := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.app_eq_appLE,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  congr 1
  simp only [w]

include w hf hW in
/-- **Base change of sections.** The map `B ⊗[A] Γ(ℱ, W) ⟶ Γ(g^* ℱ, g⁻¹ W)`,
`b ⊗ x ↦ iY^♯ b • g^* x`, for `A = Γ(S, V)` and `B = Γ(T, ⊤)`. -/
noncomputable def sectionsBaseChange :
    Γ(T, ⊤) ⊗[Γ(S, V)] Γ(ℱ, W) →+ Γ((pullback g).obj ℱ, g ⁻¹ᵁ W) :=
  TensorProduct.liftAddHom
    { toFun b :=
        { toFun x := iY.appLE ⊤ (g ⁻¹ᵁ W) (le_top.trans iY.preimage_top.ge) b • pullbackSection g x
          map_zero' := by simp only [pullbackSection, map_zero, smul_zero]
          map_add' x x' := by rw [pullbackSection_add, smul_add] }
      map_zero' := by ext x; simp
      map_add' b b' := by ext x; simp [add_smul] }
    (fun a b x ↦ by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [hW, pullbackSection_smul, smul_smul, Algebra.smul_def, hf, map_mul,
        appLE_comp_eq_app_appLE w hfV hWV, mul_comm])

lemma sectionsBaseChange_tmul (b : Γ(T, ⊤)) (x : Γ(ℱ, W)) :
    sectionsBaseChange w hfV ℱ hWV hf hW (b ⊗ₜ x) =
      iY.appLE ⊤ (g ⁻¹ᵁ W) (le_top.trans iY.preimage_top.ge) b • pullbackSection g x :=
  rfl


/-- **Base change of sections over an affine open with a free generator.** If `T` and `V` are
affine and `ℱ` has a free generator `e` on the affine open `W ⊆ iX⁻¹ V`, the map
`B ⊗[A] Γ(ℱ, W) ⟶ Γ(g^* ℱ, g⁻¹ W)` is bijective: through `e` and its pullback `g^* e`, which is a
free generator of `g^* ℱ` on `g⁻¹ W`, it is the identification of `B ⊗[A] Γ(X, W)` with the ring
of functions `Γ(Y, g⁻¹ W)` of the affine `g⁻¹ W = W ×_S T`. -/
theorem sectionsBaseChange_bijective (H : IsPullback g iY iX f) (hV : IsAffineOpen V)
    [IsAffine T] (hWa : IsAffineOpen W) {e : Γ(ℱ, W)} (he : IsFreeGenerator e) :
    Function.Bijective (sectionsBaseChange H.w hfV ℱ hWV hf hW) := by
  letI : Algebra Γ(S, V) Γ(X, W) := (iX.appLE V W hWV).hom.toAlgebra
  let ψ : Γ(X, W) →ₗ[Γ(S, V)] Γ(ℱ, W) :=
    { toFun r := r • e
      map_add' r r' := add_smul r r' e
      map_smul' a r := by
        rw [RingHom.id_apply, hW, Algebra.smul_def, mul_smul]
        rfl }
  have hψ : Function.Bijective ψ := he.bijective
  have hUY : g ⁻¹ᵁ W = g ⁻¹ᵁ W ⊓ iY ⁻¹ᵁ ⊤ := by simp
  have hpush := (isIso_pushoutSection_iff H hfV hWV hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H hfV hWV hUY hV (isAffineOpen_top T) hWa)
  have hα : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(T, ⊤)) = f.appLE V ⊤ hfV := by
    rw [hf]
    rfl
  let ε := hpush.tensorEquiv hα rfl
  have he' : IsFreeGenerator (pullbackSection g e) := he.pullback_unit_app g
  have key : ⇑(sectionsBaseChange H.w hfV ℱ hWV hf hW) ∘ ⇑(ψ.lTensor Γ(T, ⊤)) =
      (fun s : Γ(Y, g ⁻¹ᵁ W) ↦ s • pullbackSection g e) ∘ ⇑ε := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b r =>
      simp only [Function.comp_apply, LinearMap.lTensor_tmul, sectionsBaseChange_tmul]
      rw [IsPushout.tensorEquiv_tmul]
      change _ • pullbackSection g (r • e) = _
      rw [pullbackSection_smul, smul_smul, Scheme.Hom.app_eq_appLE]
    | add z z' hz hz' =>
      simp only [Function.comp_apply, map_add, add_smul] at hz hz' ⊢
      rw [hz, hz']
  have hlt : Function.Bijective (ψ.lTensor Γ(T, ⊤)) :=
    (LinearEquiv.lTensor Γ(T, ⊤) (LinearEquiv.ofBijective ψ hψ)).bijective
  refine (Function.Bijective.of_comp_iff _ hlt).mp ?_
  rw [key]
  exact he'.bijective.comp ε.bijective

end Sections

end AlgebraicGeometry.Scheme.Modules
