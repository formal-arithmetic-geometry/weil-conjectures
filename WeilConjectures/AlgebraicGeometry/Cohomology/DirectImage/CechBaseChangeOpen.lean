/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechModuleBaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechSheaf

/-!
# Base change of Čech cochains over an affine open of the new base

Consider a cartesian square of schemes
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S` affine, and an affine open `W` of `T` (`T` itself is arbitrary). Write
`A = Γ(S, ⊤)` and `B = Γ(T, W)`. For a quasi-coherent `𝒪_X`-module `ℱ` and an affine open `U` of
`X`, the map `B ⊗[A] Γ(ℱ, U) ⟶ Γ(g'^* ℱ, g'⁻¹ U ⊓ f'⁻¹ W)`, `b ⊗ m ↦ f'^♯ b • g'^* m`, is
bijective (`AlgebraicGeometry.Scheme.Modules.bijective_sectionsBaseChangeOpen`). Consequently, for
a finite family `V` of opens of `X` whose finite intersections are affine, the Čech complex of
`g'^* ℱ` for the family `f'⁻¹ W ⊓ g'⁻¹ V i` is the base change `B ⊗[A] Č(V, ℱ)`
(`AlgebraicGeometry.Scheme.Modules.cechBaseChangeOpenIso`).

This generalises `AlgebraicGeometry.Scheme.Modules.cechModuleComplexBaseChangeIso`, the case
`W = T` affine.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules) (W : T.Opens)
  [Algebra Γ(S, ⊤) Γ(T, W)] (hg : algebraMap Γ(S, ⊤) Γ(T, W) = (g.appLE ⊤ W (by simp)).hom)

include H in
/-- The two ways of pulling functions back from `S` to `g'⁻¹ U ⊓ f'⁻¹ W` agree. -/
lemma appLE_appLE_eq_of_isPullback {U : X.Opens} (a : Γ(S, ⊤)) :
    Y.presheaf.map (homOfLE (inf_le_left : g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W ≤ g' ⁻¹ᵁ U)).op
      (g'.app U (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f.appTop a))) =
      f'.appLE W (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W) inf_le_right (g.appLE ⊤ W (by simp) a) := by
  have h₁ : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f.appTop a) =
      f.appLE ⊤ U (by simp) a := rfl
  have h₂ : Y.presheaf.map (homOfLE (inf_le_left : g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W ≤ g' ⁻¹ᵁ U)).op
      (g'.app U (f.appLE ⊤ U (by simp) a)) =
      g'.appLE U (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W) inf_le_left (f.appLE ⊤ U (by simp) a) := by
    rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  rw [h₁, h₂, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE]
  congr 2
  exact H.w

include H hg in
/-- The functions on `S` act compatibly on the sections of `ℱ` over `U` and of `g'^* ℱ` over
`g'⁻¹ U ⊓ f'⁻¹ W`. -/
lemma presheaf_map_pullbackSection_smul {U : X.Opens} (a : Γ(S, ⊤))
    (m : sectionsModule f ℱ U) :
    ((pullback g').obj ℱ).presheaf.map (homOfLE inf_le_left).op
      (pullbackSection (M := ℱ) (U := U) g' (a • m)) =
      f'.appLE W (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W) inf_le_right (algebraMap Γ(S, ⊤) Γ(T, W) a) •
        ((pullback g').obj ℱ).presheaf.map (homOfLE inf_le_left).op
          (pullbackSection (M := ℱ) (U := U) g' m) := by
  change ((pullback g').obj ℱ).presheaf.map _ (pullbackSection g'
    (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f.appTop a) • (m : Γ(ℱ, U)))) = _
  rw [pullbackSection_smul, map_smul, appLE_appLE_eq_of_isPullback H W a, hg]
  rfl

/-- The base change of sections `B ⊗[A] Γ(ℱ, U) ⟶ Γ(g'^* ℱ, g'⁻¹ U ⊓ f'⁻¹ W)`,
`b ⊗ m ↦ f'^♯ b • g'^* m`, for `A = Γ(S, ⊤)` and `B = Γ(T, W)`. -/
noncomputable def sectionsBaseChangeOpen (U : X.Opens) :
    Γ(T, W) ⊗[Γ(S, ⊤)] sectionsModule f ℱ U →+
      Γ((pullback g').obj ℱ, g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W) :=
  TensorProduct.liftAddHom
    { toFun b :=
        { toFun m := f'.appLE W (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W) inf_le_right b •
            ((pullback g').obj ℱ).presheaf.map (homOfLE inf_le_left).op
              (pullbackSection (M := ℱ) (U := U) g' m)
          map_zero' := by
            change _ • ((pullback g').obj ℱ).presheaf.map _ (pullbackSection g' (0 : Γ(ℱ, U))) = 0
            rw [show pullbackSection g' (0 : Γ(ℱ, U)) = 0 from map_zero _, map_zero, smul_zero]
          map_add' m m' := by
            change _ • ((pullback g').obj ℱ).presheaf.map _
              (pullbackSection g' ((m : Γ(ℱ, U)) + m')) = _
            rw [pullbackSection_add, map_add, smul_add]
            rfl }
      map_zero' := by
        ext m
        exact zero_smul _ _
      map_add' b b' := by
        ext m
        change (f'.appLE _ _ _ (b + b')) • _ = _ • _ + _ • _
        rw [map_add, add_smul] }
    (fun a b m ↦ by
      change f'.appLE _ _ _ (a • b) • _ = f'.appLE _ _ _ b • _
      rw [presheaf_map_pullbackSection_smul H ℱ W hg, smul_smul, Algebra.smul_def, map_mul,
        mul_comm])

lemma sectionsBaseChangeOpen_tmul (U : X.Opens) (b : Γ(T, W)) (m : sectionsModule f ℱ U) :
    sectionsBaseChangeOpen H ℱ W hg U (b ⊗ₜ m) =
      f'.appLE W (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W) inf_le_right b •
        ((pullback g').obj ℱ).presheaf.map (homOfLE inf_le_left).op
          (pullbackSection (M := ℱ) (U := U) g' m) :=
  TensorProduct.liftAddHom_tmul _ _ _ _

/-- **Base change of sections over affine opens.** If `S` is affine, `ℱ` quasi-coherent and `U`,
`W` are affine opens of `X` and `T`, the map `B ⊗[A] Γ(ℱ, U) ⟶ Γ(g'^* ℱ, g'⁻¹ U ⊓ f'⁻¹ W)` is
bijective: `g'⁻¹ U ⊓ f'⁻¹ W = U ×_S W` is affine with ring of functions `Γ(X, U) ⊗[A] B`. -/
theorem bijective_sectionsBaseChangeOpen [IsAffine S]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (hW : IsAffineOpen W) {U : X.Opens}
    (hU : IsAffineOpen U) :
    Function.Bijective (sectionsBaseChangeOpen H ℱ W hg U) := by
  have hUY : g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W = g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W := rfl
  have hpush := (isIso_pushoutSection_iff H (US := ⊤) (UT := W) (by simp) (by simp) hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ hUY (isAffineOpen_top S) hW hU)
  have hY : IsAffineOpen (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W) :=
    .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := W) (by simp) (by simp)
      hUY).isoPullback.hom
  let : Algebra Γ(S, ⊤) Γ(X, U) := (f.appLE ⊤ U (by simp)).hom.toAlgebra
  let : Module Γ(X, U) (sectionsModule f ℱ U) := inferInstanceAs (Module Γ(X, U) Γ(ℱ, U))
  have : IsScalarTower Γ(S, ⊤) Γ(X, U) (sectionsModule f ℱ U) := ⟨fun a r m ↦ by
    change (f.appLE ⊤ U _ a * r) • (m : Γ(ℱ, U)) =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f.appTop a) • r • (m : Γ(ℱ, U))
    rw [mul_smul]
    rfl⟩
  -- the sections of the pullback
  obtain ⟨e₁, he₁⟩ := exists_linearEquiv_pullback_sections g' ℱ hU hY inf_le_left
  -- the ring of functions of `U ×_S W`
  let ε := hpush.flip.tensorEquiv (A' := Γ(X, U)) (E := Γ(T, W)) rfl (by
    rw [hg]
    rfl)
  have hε (r : Γ(X, U)) (b : Γ(T, W)) : ε (r ⊗ₜ b) = g'.appLE U (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W)
      inf_le_left r * f'.appLE W (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W) inf_le_right b :=
    hpush.flip.tensorEquiv_tmul _ _ r b
  let : Algebra Γ(X, U) Γ(Y, g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W) :=
    (g'.appLE U (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W) inf_le_left).hom.toAlgebra
  let εₗ : Γ(X, U) ⊗[Γ(S, ⊤)] Γ(T, W) ≃ₗ[Γ(X, U)] Γ(Y, g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W) :=
    { ε.toAddEquiv with
      map_smul' r x := by
        change ε (r • x) = r • ε x
        rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, hε, map_one, mul_one, Algebra.smul_def]
        rfl }
  let Φ : Γ(T, W) ⊗[Γ(S, ⊤)] sectionsModule f ℱ U ≃+
      Γ((pullback g').obj ℱ, g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W) :=
    (TensorProduct.comm Γ(S, ⊤) Γ(T, W) (sectionsModule f ℱ U)).toAddEquiv.trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) Γ(X, U) Γ(X, U)
        (sectionsModule f ℱ U) Γ(T, W)).symm.toAddEquiv.trans
      ((εₗ.lTensor (sectionsModule f ℱ U)).toAddEquiv.trans
      ((TensorProduct.comm Γ(X, U) (sectionsModule f ℱ U)
        Γ(Y, g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W)).toAddEquiv.trans e₁.toAddEquiv)))
  suffices h : ∀ x, sectionsBaseChangeOpen H ℱ W hg U x = Φ x by
    have : ⇑(sectionsBaseChangeOpen H ℱ W hg U) = ⇑Φ := funext h
    rw [this]
    exact Φ.bijective
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b m =>
    rw [sectionsBaseChangeOpen_tmul]
    change _ = e₁ (TensorProduct.comm _ _ _ (εₗ.lTensor _
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange Γ(S, ⊤) Γ(X, U) Γ(X, U)
        (sectionsModule f ℱ U) Γ(T, W)).symm (m ⊗ₜ b))))
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.lTensor_tmul,
      TensorProduct.comm_tmul]
    change _ = e₁ (ε (1 ⊗ₜ b) ⊗ₜ (m : Γ(ℱ, U)))
    rw [hε, map_one, one_mul, ← mul_one (f'.appLE W (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W) _ b), ← smul_eq_mul,
      ← TensorProduct.smul_tmul', e₁.map_smul, he₁]

/-! ### Čech cochains -/

section Cech

variable {ι : Type u} (V : ι → X.Opens)

lemma iInf_inf_preimage_le {k : ℕ} (y : Fin (k + 1) → ι) :
    ⨅ l, (f' ⁻¹ᵁ W ⊓ g' ⁻¹ᵁ V (y l)) ≤ g' ⁻¹ᵁ (⨅ l, V (y l)) ⊓ f' ⁻¹ᵁ W := by
  rw [← iInf_preimage_eq_preimage_iInf]
  exact le_inf (le_iInf fun l ↦ (iInf_le _ l).trans inf_le_right)
    ((iInf_le _ 0).trans inf_le_left)

lemma le_iInf_inf_preimage {k : ℕ} (y : Fin (k + 1) → ι) :
    g' ⁻¹ᵁ (⨅ l, V (y l)) ⊓ f' ⁻¹ᵁ W ≤ ⨅ l, (f' ⁻¹ᵁ W ⊓ g' ⁻¹ᵁ V (y l)) := by
  rw [← iInf_preimage_eq_preimage_iInf]
  exact le_iInf fun l ↦ le_inf inf_le_right (inf_le_left.trans (iInf_le _ l))

/-- The base change of Čech cochains `B ⊗[A] Č^k(V, ℱ) ⟶ Č^k(f'⁻¹ W ⊓ g'⁻¹ V, g'^* ℱ)`. -/
noncomputable def cechBaseChangeOpen (k : ℕ) :
    Γ(T, W) ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, V (y l))) →+
      TopCat.Presheaf.CechCochain (fun i ↦ f' ⁻¹ᵁ W ⊓ g' ⁻¹ᵁ V i)
        ((pullback g').obj ℱ).presheaf k :=
  AddMonoidHom.pi fun y ↦
    (((pullback g').obj ℱ).presheaf.map (homOfLE (iInf_inf_preimage_le W V y)).op).hom.comp
      ((sectionsBaseChangeOpen H ℱ W hg (⨅ l, V (y l))).comp
        ((LinearMap.proj (R := Γ(S, ⊤)) y).baseChange Γ(T, W)).toAddMonoidHom)

lemma cechBaseChangeOpen_tmul (k : ℕ) (b : Γ(T, W))
    (c : ∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, V (y l))) (y : Fin (k + 1) → ι) :
    cechBaseChangeOpen H ℱ W hg V k (b ⊗ₜ c) y =
      ((pullback g').obj ℱ).presheaf.map (homOfLE (iInf_inf_preimage_le W V y)).op
        (sectionsBaseChangeOpen H ℱ W hg _ (b ⊗ₜ c y)) := rfl

/-- **Base change of Čech cochains over an affine open is bijective**, when `S` is affine, `ℱ`
quasi-coherent and the finite intersections of the finitely many `V i` are affine. -/
theorem bijective_cechBaseChangeOpen [IsAffine S]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] [Finite ι] (hW : IsAffineOpen W)
    (hV : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, V (y l))) (k : ℕ) :
    Function.Bijective (cechBaseChangeOpen H ℱ W hg V k) := by
  classical
  have := Fintype.ofFinite ι
  let e := (TensorProduct.piRight Γ(S, ⊤) Γ(T, W) Γ(T, W)
    (fun y : Fin (k + 1) → ι ↦ sectionsModule f ℱ (⨅ l, V (y l)))).toAddEquiv.trans
    (AddEquiv.piCongrRight fun y ↦ (AddEquiv.ofBijective _
      (bijective_sectionsBaseChangeOpen H ℱ W hg hW (hV k y))).trans
      (AddEquiv.ofBijective _ (bijective_presheaf_map_of_eq ((pullback g').obj ℱ)
        (iInf_inf_preimage_le W V y) (le_iInf_inf_preimage W V y))))
  suffices h : ∀ x, cechBaseChangeOpen H ℱ W hg V k x = e x by
    have : ⇑(cechBaseChangeOpen H ℱ W hg V k) = ⇑e := funext h
    rw [this]
    exact e.bijective
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b c =>
    funext y
    rw [cechBaseChangeOpen_tmul]
    rfl

/-- **Base change of Čech cochains commutes with the differentials.** -/
theorem cechBaseChangeOpen_d (k : ℕ)
    (x : Γ(T, W) ⊗[Γ(S, ⊤)] (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, V (y l)))) :
    cechBaseChangeOpen H ℱ W hg V (k + 1) ((cechModuleD f ℱ V k).baseChange Γ(T, W) x) =
      ((TopCat.Presheaf.cechComplex (fun i ↦ f' ⁻¹ᵁ W ⊓ g' ⁻¹ᵁ V i)).obj
        ((pullback g').obj ℱ).presheaf).d k (k + 1) (cechBaseChangeOpen H ℱ W hg V k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b c =>
    funext y
    rw [LinearMap.baseChange_tmul, cechBaseChangeOpen_tmul, TopCat.Presheaf.cechComplex_d_apply,
      cechModuleD_apply_apply, TensorProduct.tmul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [TensorProduct.tmul_smul, map_zsmul, map_zsmul, cechBaseChangeOpen_tmul,
      sectionsBaseChangeOpen_tmul, sectionsBaseChangeOpen_tmul, map_smul, map_smul, map_smul,
      sectionsModuleRestrict_apply, pullbackSection_map, presheaf_map_map_apply,
      presheaf_map_map_apply, presheaf_map_map_apply, presheaf_map_map_apply,
      ← Scheme.Hom.appLE_map, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
    · rfl

variable [IsAffine S] [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] [Finite ι]
  (hW : IsAffineOpen W) (hV : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, V (y l)))

/-- **Base change of the Čech complex over an affine open**, as complexes of abelian groups:
the Čech complex of `g'^* ℱ` for the family `f'⁻¹ W ⊓ g'⁻¹ V i` is `B ⊗[A] Č(V, ℱ)`. -/
noncomputable def cechBaseChangeOpenIso :
    ((forget₂ (ModuleCat.{u} Γ(T, W)) Ab).mapHomologicalComplex _).obj
      (((ModuleCat.baseChange Γ(S, ⊤) Γ(T, W)).mapHomologicalComplex _).obj
        (cechModuleComplexNat f ℱ V)) ≅
      (TopCat.Presheaf.cechComplex (fun i ↦ f' ⁻¹ᵁ W ⊓ g' ⁻¹ᵁ V i)).obj
        ((pullback g').obj ℱ).presheaf :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ (AddEquiv.ofBijective (cechBaseChangeOpen H ℱ W hg V k)
      (bijective_cechBaseChangeOpen H ℱ W hg V hW hV k)).toAddCommGrpIso)
    (by
      rintro k _ rfl
      ext x : 2
      exact (cechBaseChangeOpen_d H ℱ W hg V k x).symm.trans (by
        rw [cechModuleComplexNat_d]
        rfl) |>.symm)

lemma cechBaseChangeOpenIso_hom_f_apply (k : ℕ) (x) :
    (cechBaseChangeOpenIso H ℱ W hg V hW hV).hom.f k x = cechBaseChangeOpen H ℱ W hg V k x :=
  rfl

end Cech

end AlgebraicGeometry.Scheme.Modules
