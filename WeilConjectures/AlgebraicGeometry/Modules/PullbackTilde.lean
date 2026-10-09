/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit

/-!
# Pullback of quasi-coherent modules along morphisms of affine schemes

Let `R ⟶ S` be a ring map and `f : Spec S ⟶ Spec R` the induced morphism. The pullback of `M^~`
along `f` is `(S ⊗[R] M)^~`: both functors are left adjoint to `N ↦ Γ(N, ⊤)` viewed as an
`R`-module. On global sections, the resulting identification sends `1 ⊗ m` to the image of `m`
under the unit of the adjunction `f^* ⊣ f_*`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TensorProduct

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- The global sections over `Spec R` of the pushforward along `Spec.map φ` are the global
sections over `Spec S`, viewed as an `R`-module. -/
noncomputable def pushforwardSpecMapCompΓIso :
    pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (fun P ↦ LinearEquiv.toModuleIso
    (X₁ := (pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R)).obj P)
    (X₂ := (moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom).obj P)
    { toFun x := x
      invFun x := x
      map_add' _ _ := rfl
      map_smul' r x := by
        let y : Γ(P, ⊤) := x
        change (Spec.map φ).appTop ((ΓSpecIso R).inv r) • y = (ΓSpecIso S).inv (φ r) • y
        rw [← CommRingCat.comp_apply, ← ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
      left_inv _ := rfl
      right_inv _ := rfl }) (fun _ ↦ rfl)

/-- The adjunction `(tilde ⋙ f^*) ⊣ (Γ ⋙ restrictScalars φ)`. -/
noncomputable def tildePullbackAdjunction :
    tilde.functor R ⋙ pullback (Spec.map φ) ⊣
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
  (tilde.adjunction.comp (pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
    (pushforwardSpecMapCompΓIso φ)

/-- **Pullback of `M^~` along `Spec S ⟶ Spec R` is `(S ⊗[R] M)^~`.** -/
noncomputable def tildePullbackIso :
    tilde.functor R ⋙ pullback (Spec.map φ) ≅ ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  (tildePullbackAdjunction φ).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction)

lemma tildePullbackIso_hom_app_pullbackUnit (M : ModuleCat.{u} R) (m : M) :
    ((tildePullbackIso φ).hom.app M).app ⊤
      ((pullbackUnit (Spec.map φ) (tilde M)).app ⊤ (tilde.toOpen M ⊤ m)) =
      tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤ ((1 : S) ⊗ₜ m) := by
  have := congr($((tildePullbackAdjunction φ).unit_leftAdjointUniq_hom_app
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction) M) m)
  exact this

variable {φ} in
/-- On sections, a morphism of `𝒪_{Spec R}`-modules is `R`-linear. -/
lemma Hom.app_smul_Spec {P Q : (Spec R).Modules} (g : P ⟶ Q) (U : (Spec R).Opens) (r : R)
    (x : Γ(P, U)) : g.app U (r • x) = r • g.app U x := by
  rw [smul_Spec_def, smul_Spec_def, Hom.app_smul]

variable {φ} in
/-- On sections, a morphism of `𝒪_{Spec R}`-modules as an `R`-linear map. -/
noncomputable def Hom.appSpecₗ {P Q : (Spec R).Modules} (g : P ⟶ Q) (U : (Spec R).Opens) :
    Γ(P, U) →ₗ[R] Γ(Q, U) where
  toFun := g.app U
  map_add' := map_add _
  map_smul' := g.app_smul_Spec U

/-- The global sections of `f^* M^~` are `S ⊗[R] M`, for `f : Spec S ⟶ Spec R`. -/
noncomputable def tildePullbackΓEquiv (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars φ.hom).obj M ≃ₗ[S]
      Γ((pullback (Spec.map φ)).obj (tilde M), ⊤) :=
  (LinearEquiv.ofBijective (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤).hom
    (ConcreteCategory.bijective_of_isIso _)) ≪≫ₗ
    (LinearEquiv.ofBijective (Hom.appSpecₗ ((tildePullbackIso φ).hom.app M) ⊤)
      (ConcreteCategory.bijective_of_isIso (((tildePullbackIso φ).hom.app M).app ⊤))).symm

lemma tildePullbackΓEquiv_one_tmul (M : ModuleCat.{u} R) (m : M) :
    tildePullbackΓEquiv φ M ((1 : S) ⊗ₜ m) =
      (pullbackUnit (Spec.map φ) (tilde M)).app ⊤ (tilde.toOpen M ⊤ m) := by
  dsimp only [tildePullbackΓEquiv, LinearEquiv.trans_apply]
  exact (LinearEquiv.symm_apply_eq _).mpr (tildePullbackIso_hom_app_pullbackUnit φ M m).symm

lemma fromTildeΓ_app_toOpen (M : (Spec R).Modules) (m : Γ(M, ⊤)) :
    M.fromTildeΓ.app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m) = m := by
  have := congr($(toOpen_fromTildeΓ_app M ⊤) m)
  refine this.trans ?_
  change M.presheaf.map (homOfLE le_top).op m = m
  rw [show (homOfLE le_top : (⊤ : (Spec R).Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- **Base change for quasi-coherent modules along `Spec S ⟶ Spec R`**: the global sections of
the pullback of a quasi-coherent `𝒪_{Spec R}`-module `M` are `S ⊗[R] Γ(M, ⊤)`. -/
noncomputable def pullbackSpecΓEquiv (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) ≃ₗ[S]
      Γ((pullback (Spec.map φ)).obj M, ⊤) :=
  haveI : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  haveI : IsIso ((pullback (Spec.map φ)).map M.fromTildeΓ) := inferInstance
  tildePullbackΓEquiv φ _ ≪≫ₗ
    LinearEquiv.ofBijective (Hom.appSpecₗ ((pullback (Spec.map φ)).map M.fromTildeΓ) ⊤)
      (ConcreteCategory.bijective_of_isIso (((pullback (Spec.map φ)).map M.fromTildeΓ).app ⊤))

lemma pullbackSpecΓEquiv_one_tmul (M : (Spec R).Modules) [M.IsQuasicoherent] (m : Γ(M, ⊤)) :
    pullbackSpecΓEquiv φ M ((1 : S) ⊗ₜ m) = (pullbackUnit (Spec.map φ) M).app ⊤ m := by
  change ((pullback (Spec.map φ)).map M.fromTildeΓ).app ⊤
    (tildePullbackΓEquiv φ (moduleSpecΓFunctor.obj M) ((1 : S) ⊗ₜ m)) = _
  refine (congr_arg (((pullback (Spec.map φ)).map M.fromTildeΓ).app ⊤)
    (tildePullbackΓEquiv_one_tmul φ (moduleSpecΓFunctor.obj M) m)).trans ?_
  have := congr($(((pullbackPushforwardAdjunction (Spec.map φ)).unit.naturality
    M.fromTildeΓ)).app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m))
  refine this.symm.trans ?_
  exact congr_arg ((pullbackUnit (Spec.map φ) M).app ⊤) (fromTildeΓ_app_toOpen M m)

end Scheme.Modules

end AlgebraicGeometry
