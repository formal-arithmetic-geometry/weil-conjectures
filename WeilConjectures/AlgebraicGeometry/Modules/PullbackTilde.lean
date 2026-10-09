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

/-- For an `R`-algebra `S`, `S ⊗[R] N` is `(ModuleCat.extendScalars (algebraMap R S)).obj N`. -/
noncomputable def ModuleCat.tensorEquivExtendScalars (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (N : ModuleCat.{u} R) :
    S ⊗[R] N ≃ₗ[S] (ModuleCat.extendScalars (algebraMap R S)).obj N := by
  let T := (ModuleCat.extendScalars (algebraMap R S)).obj N
  let S' := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let toFun : S ⊗[R] N →ₗ[R] TensorProduct R S' N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S' N s
        map_add' s s' := (TensorProduct.mk R S' N).map_add s s'
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S' N) (Algebra.smul_def r s)).trans
            ((TensorProduct.mk R S' N).map_smul r (s : S')) }
  let invFun : TensorProduct R S' N →ₗ[R] S ⊗[R] N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S N (show S from s)
        map_add' s s' := (TensorProduct.mk R S N).map_add (show S from s) (show S from s')
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S N) (Algebra.smul_def r (show S from s)).symm).trans
            ((TensorProduct.mk R S N).map_smul r (show S from s)) }
  have h₁ : ∀ x, invFun (toFun x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have h₂ : ∀ x, toFun (invFun x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  exact
    { toFun := toFun
      invFun := invFun
      map_add' := toFun.map_add
      map_smul' s x := by
        induction x using TensorProduct.induction_on with
        | zero => exact (map_zero toFun).trans (show (0 : T) = s • (0 : T) from (smul_zero s).symm)
        | tmul s' n => rfl
        | add x y hx hy =>
          rw [smul_add, map_add, hx, hy, map_add]
          exact (smul_add s _ _).symm
      left_inv := h₁
      right_inv := h₂ }

lemma ModuleCat.tensorEquivExtendScalars_tmul (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (N : ModuleCat.{u} R) (s : S) (n : N) :
    ModuleCat.tensorEquivExtendScalars R S N (s ⊗ₜ n) =
      TensorProduct.tmul R (M := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S))
        s n :=
  rfl

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

section Algebra

/-- Sections of an `𝒪_{Spec R}`-module are `R`-modules, for `R` a commutative ring. -/
noncomputable instance moduleOf {R : Type u} [CommRing R] (M : (Spec (.of R)).Modules)
    (U : (Spec (.of R)).Opens) : Module R Γ(M, U) :=
  inferInstanceAs (Module (CommRingCat.of R) ((modulesSpecToSheaf.obj M).obj.obj (.op U)))

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- On global sections over `Spec A`, the unit of the adjunction for `Spec B ⟶ Spec A` is
semilinear along `algebraMap A B`. -/
lemma pullbackUnitApp_top_smul (P : (Spec (.of A)).Modules) (a : A) (x : Γ(P, ⊤)) :
    pullbackUnitApp (Spec.map (CommRingCat.ofHom (algebraMap A B))) P ⊤ (a • x) =
      algebraMap A B a • pullbackUnitApp (Spec.map (CommRingCat.ofHom (algebraMap A B))) P ⊤ x := by
  set f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  have h₁ : (a • x : Γ(P, ⊤)) = (ΓSpecIso (.of A)).inv a • x :=
    (smul_Spec_def (R := CommRingCat.of A) (M := P) (U := ⊤) a x).trans (by
      rw [show (⊤ : (Spec (.of A)).Opens).leTop = 𝟙 _ from rfl, op_id,
        CategoryTheory.Functor.map_id]
      rfl)
  have h₂ : (algebraMap A B a • pullbackUnitApp f P ⊤ x : Γ((pullback f).obj P, f ⁻¹ᵁ ⊤)) =
      (show Γ(Spec (.of B), f ⁻¹ᵁ ⊤) from (ΓSpecIso (.of B)).inv (algebraMap A B a)) •
        pullbackUnitApp f P ⊤ x :=
    (smul_Spec_def (R := CommRingCat.of B) (M := (pullback f).obj P) (U := ⊤)
      (algebraMap A B a) (pullbackUnitApp f P ⊤ x)).trans (by
      rw [show (⊤ : (Spec (.of B)).Opens).leTop = 𝟙 _ from rfl, op_id,
        CategoryTheory.Functor.map_id]
      rfl)
  rw [h₁, h₂]
  refine (Hom.app_smul (pullbackUnit f P) ((ΓSpecIso (.of A)).inv a) x).trans ?_
  have hr : f.app ⊤ ((ΓSpecIso (.of A)).inv a) = (ΓSpecIso (.of B)).inv (algebraMap A B a) :=
    (congr($(ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))) a)).symm
  exact congrArg (fun r : Γ(Spec (.of B), f ⁻¹ᵁ ⊤) ↦ r • pullbackUnitApp f P ⊤ x) hr

/-- **Base change for quasi-coherent modules along `Spec B ⟶ Spec A`**, for an `A`-algebra `B`:
the global sections of the pullback of a quasi-coherent `𝒪_{Spec A}`-module `M` are
`B ⊗[A] Γ(M, ⊤)`, with `1 ⊗ m` corresponding to the image of `m` under the unit. -/
theorem exists_linearEquiv_pullback_Spec (M : (Spec (.of A)).Modules) [M.IsQuasicoherent] :
    ∃ e : B ⊗[A] Γ(M, ⊤) ≃ₗ[B]
      Γ((pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M, ⊤),
      ∀ m : Γ(M, ⊤), e (1 ⊗ₜ m) =
        pullbackUnitApp (Spec.map (CommRingCat.ofHom (algebraMap A B))) M ⊤ m := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let e₁ : (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) ≃ₗ[B]
      Γ((pullback (Spec.map φ)).obj M, ⊤) := pullbackSpecΓEquiv φ M
  let e₀ : B ⊗[A] Γ(M, ⊤) ≃ₗ[B] (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) :=
    ModuleCat.tensorEquivExtendScalars A B (ModuleCat.of A Γ(M, ⊤))
  exact ⟨e₀ ≪≫ₗ e₁, fun m ↦ pullbackSpecΓEquiv_one_tmul φ M m⟩

end Algebra

end Scheme.Modules

end AlgebraicGeometry
