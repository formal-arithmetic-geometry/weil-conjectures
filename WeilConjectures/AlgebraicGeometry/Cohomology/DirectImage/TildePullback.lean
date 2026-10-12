/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import WeilConjectures.Algebra.Homology.FlatComplexBaseChange

/-!
# Pulling back `M^~` along a morphism to an affine scheme

Let `R` be a ring and `h : Y ⟶ Spec R` a morphism of schemes. The functor `M ↦ h^* M^~`
(`AlgebraicGeometry.Scheme.Modules.tildePullback`) from `R`-modules to `𝒪_Y`-modules is left
adjoint to the functor of global sections, viewed as `R`-modules through `h`
(`AlgebraicGeometry.Scheme.Modules.tildePullbackAdjunction`). Over an affine open `W` of `Y`, its
sections are `Γ(Y, W) ⊗[R] M` (`AlgebraicGeometry.Scheme.Modules.bijective_tildePullbackSections`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {Y : Scheme.{u}} (h : Y ⟶ Spec R)

/-- The functor `M ↦ h^* M^~` for `h : Y ⟶ Spec R`. -/
noncomputable abbrev tildePullback : ModuleCat.{u} R ⥤ Y.Modules :=
  tilde.functor R ⋙ pullback h

/-- The global sections functor of `Y`, with values in `R`-modules through `h : Y ⟶ Spec R`. -/
noncomputable abbrev sectionsOver : Y.Modules ⥤ ModuleCat.{u} R :=
  pushforward h ⋙ moduleSpecΓFunctor

/-- The adjunction `(M ↦ h^* M^~) ⊣ (N ↦ Γ(Y, N))`. -/
noncomputable def tildePullbackAdjunction : tildePullback h ⊣ sectionsOver h :=
  tilde.adjunction.comp (pullbackPushforwardAdjunction h)

/-- The section `h^* m` of `h^* M^~` over `Y` attached to an element `m` of `M`. -/
noncomputable def tildePullbackSection (M : ModuleCat.{u} R) (m : M) :
    Γ((tildePullback h).obj M, h ⁻¹ᵁ ⊤) :=
  pullbackSection h (M := tilde M) (U := ⊤) (tilde.toOpen M ⊤ m)

lemma tildePullbackSection_add (M : ModuleCat.{u} R) (m m' : M) :
    tildePullbackSection h M (m + m') =
      tildePullbackSection h M m + tildePullbackSection h M m' := by
  rw [tildePullbackSection, map_add, pullbackSection_add]
  rfl

lemma tildePullbackSection_zero (M : ModuleCat.{u} R) :
    tildePullbackSection h M 0 = 0 := by
  rw [tildePullbackSection, map_zero]
  exact map_zero _

lemma tildePullback_map_app_tildePullbackSection {M N : ModuleCat.{u} R} (φ : M ⟶ N) (m : M) :
    ((tildePullback h).map φ).app (h ⁻¹ᵁ ⊤) (tildePullbackSection h M m) =
      tildePullbackSection h N (φ m) := by
  rw [tildePullbackSection, tildePullbackSection, Functor.comp_map,
    pullback_map_app_pullbackSection]
  congr 1
  exact congr($(tilde.toOpen_map_app φ ⊤) m)

/-- The morphism `h^* M^~ ⟶ N` adjoint to an `R`-linear map `M ⟶ Γ(Y, N)` sends `h^* m` to the
image of `m`. -/
lemma tildePullbackAdjunction_homEquiv_symm_app (M : ModuleCat.{u} R) (N : Y.Modules)
    (γ : M ⟶ (sectionsOver h).obj N) (m : M) :
    (((tildePullbackAdjunction h).homEquiv M N).symm γ).app (h ⁻¹ᵁ ⊤)
      (tildePullbackSection h M m) = (show Γ(N, h ⁻¹ᵁ ⊤) from γ m) := by
  rw [tildePullbackAdjunction, Adjunction.comp_homEquiv, Equiv.symm_trans_apply]
  set a := (tilde.adjunction.homEquiv M ((pushforward h).obj N)).symm γ
  have ha : γ = tilde.adjunction.homEquiv M ((pushforward h).obj N) a := by
    rw [Equiv.apply_symm_apply]
  have h₁ := (pullbackPushforwardAdjunction h).homEquiv_unit (tilde M) N
    (((pullbackPushforwardAdjunction h).homEquiv _ _).symm a)
  rw [Equiv.apply_symm_apply] at h₁
  have h₂ := congr($(h₁).app ⊤ (tilde.toOpen M ⊤ m))
  rw [ha, Adjunction.homEquiv_unit]
  exact h₂.symm.trans rfl

/-! ### Sections over an affine open -/

variable (W : Y.Opens) [Algebra R Γ(Y, W)]
  (hR : ∀ r : R, algebraMap R Γ(Y, W) r = h.appLE ⊤ W (by simp) ((Scheme.ΓSpecIso R).inv r))

/-- The restriction of `h^* m` to `W`. -/
noncomputable def tildePullbackSectionRes (M : ModuleCat.{u} R) (m : M) :
    Γ((tildePullback h).obj M, W) :=
  ((tildePullback h).obj M).presheaf.map (homOfLE (by simp : W ≤ h ⁻¹ᵁ ⊤)).op
    (tildePullbackSection h M m)

include hR in
lemma tildePullbackSectionRes_smul (M : ModuleCat.{u} R) (r : R) (m : M) :
    tildePullbackSectionRes h W M (r • m) =
      algebraMap R Γ(Y, W) r • tildePullbackSectionRes h W M m := by
  rw [tildePullbackSectionRes, tildePullbackSectionRes, tildePullbackSection,
    tildePullbackSection, map_smul, hR]
  have : (tilde.toOpen M ⊤ (r • m) : Γ(tilde M, ⊤)) =
      (Scheme.ΓSpecIso R).inv r • (tilde.toOpen M ⊤ m : Γ(tilde M, ⊤)) := by
    rw [LinearMap.map_smul]
    rfl
  rw [this, pullbackSection_smul, map_smul]
  congr 1
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

include hR in
/-- The map `Γ(Y, W) ⊗[R] M ⟶ Γ(h^* M^~, W)`, `b ⊗ m ↦ b • h^* m`. -/
noncomputable def tildePullbackSections (M : ModuleCat.{u} R) :
    Γ(Y, W) ⊗[R] M →+ Γ((tildePullback h).obj M, W) :=
  TensorProduct.liftAddHom
    { toFun b :=
        { toFun m := b • tildePullbackSectionRes h W M m
          map_zero' := by
            rw [tildePullbackSectionRes, tildePullbackSection_zero, map_zero, smul_zero]
          map_add' m m' := by
            rw [tildePullbackSectionRes, tildePullbackSection_add, map_add, smul_add]
            rfl }
      map_zero' := by
        ext m
        exact zero_smul _ _
      map_add' b b' := by
        ext m
        exact add_smul _ _ _ }
    (fun r b m ↦ by
      change (r • b) • _ = b • _
      rw [tildePullbackSectionRes_smul h W hR, smul_smul, Algebra.smul_def, mul_comm])

lemma tildePullbackSections_tmul (M : ModuleCat.{u} R) (b : Γ(Y, W)) (m : M) :
    tildePullbackSections h W hR M (b ⊗ₜ m) = b • tildePullbackSectionRes h W M m :=
  TensorProduct.liftAddHom_tmul _ _ _ _

lemma tildePullbackSections_smul (M : ModuleCat.{u} R) (b : Γ(Y, W))
    (x : Γ(Y, W) ⊗[R] M) :
    tildePullbackSections h W hR M (b • x) = b • tildePullbackSections h W hR M x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul b' m =>
    rw [TensorProduct.smul_tmul', tildePullbackSections_tmul, tildePullbackSections_tmul,
      smul_eq_mul, mul_smul]

lemma tildePullbackSections_naturality {M N : ModuleCat.{u} R} (φ : M ⟶ N)
    (x : Γ(Y, W) ⊗[R] M) :
    ((tildePullback h).map φ).app W (tildePullbackSections h W hR M x) =
      tildePullbackSections h W hR N (φ.hom.baseChange Γ(Y, W) x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  | tmul b m =>
    rw [tildePullbackSections_tmul, LinearMap.baseChange_tmul, tildePullbackSections_tmul,
      Hom.app_smul, tildePullbackSectionRes, tildePullbackSectionRes, Hom.app_presheaf_map,
      tildePullback_map_app_tildePullbackSection]
    rfl

include hR in
/-- **Sections of `h^* M^~` over an affine open.** For an affine open `W` of `Y`, the map
`Γ(Y, W) ⊗[R] M ⟶ Γ(h^* M^~, W)` is bijective. -/
theorem bijective_tildePullbackSections (hW : IsAffineOpen W) (M : ModuleCat.{u} R) :
    Function.Bijective (tildePullbackSections h W hR M) := by
  let : Algebra Γ(Spec R, ⊤) Γ(Y, W) := (h.appLE ⊤ W (by simp)).hom.toAlgebra
  obtain ⟨e, he⟩ := exists_linearEquiv_pullback_sections h (tilde M) (isAffineOpen_top _) hW
    (by simp)
  -- change of rings along `R ≅ Γ(Spec R, ⊤)` and of modules along `M ≅ Γ(M^~, ⊤)`
  let t : M ≃+ Γ(tilde M, ⊤) := (tilde.isoTop M).toLinearEquiv.toAddEquiv
  have ht (m : M) : t m = tilde.toOpen M ⊤ m := rfl
  have ht_smul (r : R) (m : M) : t (r • m) = (Scheme.ΓSpecIso R).inv r • t m := by
    rw [ht, ht, LinearMap.map_smul]
    rfl
  let τ : Γ(Y, W) ⊗[R] M →+ Γ(Y, W) ⊗[Γ(Spec R, ⊤)] Γ(tilde M, ⊤) :=
    TensorProduct.liftAddHom
      { toFun b := (TensorProduct.mk Γ(Spec R, ⊤) Γ(Y, W) Γ(tilde M, ⊤) b).toAddMonoidHom.comp
          t.toAddMonoidHom
        map_zero' := by ext m; simp
        map_add' b b' := by ext m; simp [TensorProduct.add_tmul] }
      (fun r b m ↦ by
        change (r • b) ⊗ₜ t m = b ⊗ₜ t (r • m)
        rw [ht_smul, ← TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def, hR]
        rfl)
  let τ' : Γ(Y, W) ⊗[Γ(Spec R, ⊤)] Γ(tilde M, ⊤) →+ Γ(Y, W) ⊗[R] M :=
    TensorProduct.liftAddHom
      { toFun b := (TensorProduct.mk R Γ(Y, W) M b).toAddMonoidHom.comp t.symm.toAddMonoidHom
        map_zero' := by ext m; simp
        map_add' b b' := by ext m; simp [TensorProduct.add_tmul] }
      (fun r' b x ↦ by
        change (r' • b) ⊗ₜ t.symm x = b ⊗ₜ t.symm (r' • x)
        obtain ⟨r, rfl⟩ : ∃ r, (Scheme.ΓSpecIso R).inv r = r' :=
          ⟨(Scheme.ΓSpecIso R).hom r', by simp⟩
        obtain ⟨m, rfl⟩ := t.surjective x
        rw [← ht_smul, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
          ← TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def, hR]
        rfl)
  have hττ' : Function.LeftInverse τ' τ := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul b m =>
      change τ' (b ⊗ₜ t m) = b ⊗ₜ m
      change b ⊗ₜ t.symm (t m) = b ⊗ₜ m
      rw [AddEquiv.symm_apply_apply]
  have hτ'τ : Function.RightInverse τ' τ := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul b x =>
      change b ⊗ₜ t (t.symm x) = b ⊗ₜ x
      rw [AddEquiv.apply_symm_apply]
  have hτ : Function.Bijective τ := ⟨hττ'.injective, hτ'τ.surjective⟩
  suffices h : ⇑(tildePullbackSections h W hR M) = ⇑e ∘ ⇑τ by
    rw [h]
    exact e.bijective.comp hτ
  funext x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, Function.comp_apply, map_zero, map_zero]
  | add x y hx hy =>
    rw [map_add, hx, hy, Function.comp_apply, Function.comp_apply, Function.comp_apply, map_add,
      map_add]
  | tmul b m =>
    rw [tildePullbackSections_tmul, Function.comp_apply]
    change _ = e (b ⊗ₜ t m)
    rw [← mul_one b, ← smul_eq_mul, ← TensorProduct.smul_tmul', e.map_smul, he]
    rfl

end AlgebraicGeometry.Scheme.Modules
