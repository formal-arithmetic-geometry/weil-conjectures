/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomology.InjectiveTorsion

/-!
# Injective sheaves of `ℤ/n`-modules are acyclic as abelian sheaves

Let `I` be an injective sheaf of `ℤ/n`-modules (`n ≠ 0`) on a site. Its underlying abelian sheaf
has no higher cohomology. Embed the underlying abelian sheaf of `I` into an injective abelian
sheaf `F`. Coinduction `R = Hom_ℤ(ℤ/n, -)` is right adjoint to the forgetful functor, so this
embedding gives a monomorphism `I ⟶ R F` of sheaves of `ℤ/n`-modules, which splits since `I` is
injective. Hence the underlying abelian sheaf of `I` is a retract of that of `R F`, which is the
`n`-torsion `F[n]` (`CategoryTheory.Sheaf.shortExact_coindCounit`), and `F[n]` is acyclic
(`CategoryTheory.Abelian.Ext.subsingleton_of_shortExact_smul`).

## Main definitions

- `coindZMod`: coinduction from abelian groups to `ℤ/n`-modules, right adjoint to the forgetful
  functor (`forget₂CoindZModAdj`).

## Main statements

- `CategoryTheory.Sheaf.subsingleton_H_forget₂_of_injective`: the acyclicity.
-/

@[expose] public section

open CategoryTheory
universe w

/-- Coinduction from abelian groups to `ℤ/n`-modules, `A ↦ Hom_ℤ(ℤ/n, A)`. -/
noncomputable def coindZMod (n : ℕ) : AddCommGrpCat.{w} ⥤ ModuleCat.{w} (ULift.{w} (ZMod n)) :=
  (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence.inverse ⋙
    ModuleCat.coextendScalars (algebraMap ℤ (ULift.{w} (ZMod n)))

noncomputable def forget₂CoindZModAdj (n : ℕ) :
    forget₂ (ModuleCat.{w} (ULift.{w} (ZMod n))) AddCommGrpCat.{w} ⊣ coindZMod.{w} n :=
  ((ModuleCat.restrictCoextendScalarsAdj.{w} (algebraMap ℤ (ULift.{w} (ZMod n)))).comp
    (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence.toAdjunction).ofNatIsoLeft
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl))

/-- An additive map out of `ℤ/n` is determined by its value at `1`. -/
lemma ULift.ZMod.addMonoidHom_ext {n : ℕ} {M : Type*} [AddCommGroup M]
    {φ ψ : ULift.{w} (ZMod n) →+ M} (h : φ 1 = ψ 1) : φ = ψ := by
  ext ⟨x⟩
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  have hk : (⟨(k : ZMod n)⟩ : ULift.{w} (ZMod n)) = k • (1 : ULift.{w} (ZMod n)) := by
    ext; simp
  rw [hk, map_zsmul, map_zsmul, h]

/-- Every `n`-torsion element is the value at `1` of an additive map out of `ℤ/n`. -/
lemma ULift.ZMod.exists_addMonoidHom_apply_one {n : ℕ} {M : Type*} [AddCommGroup M]
    {a : M} (ha : (n : ℤ) • a = 0) : ∃ φ : ULift.{w} (ZMod n) →+ M, φ 1 = a := by
  let g : ℤ →+ M := zmultiplesHom M a
  have hg : g n = 0 := by simpa [g] using ha
  refine ⟨(ZMod.lift n ⟨g, hg⟩).comp (AddEquiv.ulift.toAddMonoidHom), ?_⟩
  change ZMod.lift n ⟨g, hg⟩ ((1 : ULift.{w} (ZMod n)).down) = a
  have : ((1 : ULift.{w} (ZMod n)).down) = ((1 : ℤ) : ZMod n) := by simp
  rw [this, ZMod.lift_coe]
  simp [g]

lemma forget₂CoindZModAdj_counit_app (n : ℕ) (A : AddCommGrpCat.{w}) :
    (forget₂CoindZModAdj.{w} n).counit.app A =
      (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).map
        ((ModuleCat.RestrictionCoextensionAdj.counit'
          (algebraMap ℤ (ULift.{w} (ZMod n)))).app
          ((forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence.inverse.obj A)) ≫
        (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence.counit.app A := by
  simp [forget₂CoindZModAdj, Adjunction.comp_counit_app, ModuleCat.restrictCoextendScalarsAdj]
  rfl

lemma counit'_app_apply (n : ℕ) (M : ModuleCat.{w} ℤ)
    (φ : (ModuleCat.restrictScalars (algebraMap ℤ (ULift.{w} (ZMod n)))).obj
      ((ModuleCat.coextendScalars (algebraMap ℤ (ULift.{w} (ZMod n)))).obj M)) :
    (ModuleCat.RestrictionCoextensionAdj.counit' (algebraMap ℤ (ULift.{w} (ZMod n)))).app M φ =
      (ModuleCat.CoextendScalars.equiv (algebraMap ℤ (ULift.{w} (ZMod n))) M φ)
        (show _ from (1 : ULift.{w} (ZMod n))) := rfl

lemma forget₂CoindZModAdj_counit_shortExact (n : ℕ) (A : AddCommGrpCat.{w}) :
    Function.Injective ((forget₂CoindZModAdj.{w} n).counit.app A) ∧
      ∀ a : A, (n : ℤ) • a = 0 → a ∈ Set.range ((forget₂CoindZModAdj.{w} n).counit.app A) := by
  set M := (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence.inverse.obj A
  set ε := (forget₂ (ModuleCat.{w} ℤ) AddCommGrpCat.{w}).asEquivalence.counit.app A
  have hε := ConcreteCategory.bijective_of_isIso ε
  rw [forget₂CoindZModAdj_counit_app]
  refine ⟨fun φ ψ h ↦ ?_, fun a ha ↦ ?_⟩
  · have h' := hε.1 h
    change (ModuleCat.CoextendScalars.equiv _ M φ) (show _ from (1 : ULift.{w} (ZMod n))) =
      (ModuleCat.CoextendScalars.equiv _ M ψ) (show _ from (1 : ULift.{w} (ZMod n))) at h'
    apply (ModuleCat.CoextendScalars.equiv _ M).injective
    exact LinearMap.toAddMonoidHom_injective
      (ULift.ZMod.addMonoidHom_ext.{w} (n := n) (M := M) h')
  · obtain ⟨b, rfl⟩ := hε.2 a
    have hb : (n : ℤ) • b = 0 := hε.1 (by rw [map_zsmul, ha, map_zero])
    obtain ⟨φ, hφ⟩ := ULift.ZMod.exists_addMonoidHom_apply_one.{w} (n := n) (M := M) hb
    refine ⟨(ModuleCat.CoextendScalars.equiv _ M).symm
      { toFun := fun x ↦ φ (show ULift.{w} (ZMod n) from x)
        map_add' := fun x y ↦ φ.map_add _ _
        map_smul' := fun k x ↦ ?_ }, ?_⟩
    · rw [ModuleCat.restrictScalars.smul_def]
      change φ ((algebraMap ℤ (ULift.{w} (ZMod n)) k) * (show ULift.{w} (ZMod n) from x)) = _
      rw [algebraMap_int_eq, eq_intCast, ← zsmul_eq_mul, map_zsmul, RingHom.id_apply]
      exact (int_smul_eq_zsmul _ _ _).symm
    erw [ConcreteCategory.comp_apply]
    refine congrArg ε ?_
    have key : (ModuleCat.RestrictionCoextensionAdj.counit'
        (algebraMap ℤ (ULift.{w} (ZMod n)))).app M ((ModuleCat.CoextendScalars.equiv _ M).symm
          { toFun := fun x ↦ φ (show ULift.{w} (ZMod n) from x)
            map_add' := fun x y ↦ φ.map_add _ _
            map_smul' := fun k x ↦ by
              rw [ModuleCat.restrictScalars.smul_def]
              change φ ((algebraMap ℤ (ULift.{w} (ZMod n)) k) *
                (show ULift.{w} (ZMod n) from x)) = _
              rw [algebraMap_int_eq, eq_intCast, ← zsmul_eq_mul, map_zsmul, RingHom.id_apply]
              exact (int_smul_eq_zsmul _ _ _).symm }) = b := by
      refine (counit'_app_apply n M _).trans ?_
      rw [LinearEquiv.apply_symm_apply]
      exact hφ
    exact key
universe u
namespace CategoryTheory.Sheaf
variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) (n : ℕ)
  [J.HasSheafCompose (coindZMod.{u + 1} n)]

/-- For a mono `forget I ⟶ F`, the induced map `I ⟶ R F` of sheaves of `ℤ/n`-modules is a mono. -/
noncomputable def toCoind
    (I : Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))
    {F : Sheaf J AddCommGrpCat.{u + 1}}
    (f : (sheafCompose J (forget₂ _ AddCommGrpCat.{u + 1})).obj I ⟶ F) :
    I ⟶ (sheafCompose J (coindZMod.{u + 1} n)).obj F :=
  ⟨Functor.whiskerLeft I.obj (forget₂CoindZModAdj.{u + 1} n).unit ≫
    Functor.whiskerRight f.hom (coindZMod.{u + 1} n)⟩

lemma mono_toCoind (I : Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))
    {F : Sheaf J AddCommGrpCat.{u + 1}}
    (f : (sheafCompose J (forget₂ _ AddCommGrpCat.{u + 1})).obj I ⟶ F) [Mono f] :
    Mono (toCoind J n I f) := by
  have : Mono f.hom := (sheafToPresheaf J _).map_mono f
  have : (coindZMod.{u + 1} n).IsRightAdjoint := (forget₂CoindZModAdj.{u + 1} n).isRightAdjoint
  have h₁ : Mono (I.obj.whiskerLeft (forget₂CoindZModAdj.{u + 1} n).unit) := by
    rw [NatTrans.mono_iff_mono_app]; intro U; dsimp; infer_instance
  have h₂ : Mono (Functor.whiskerRight f.hom (coindZMod.{u + 1} n)) := by
    rw [NatTrans.mono_iff_mono_app]; intro U
    have : Mono (f.hom.app U) := (NatTrans.mono_iff_mono_app _).1 inferInstance U
    dsimp; infer_instance
  have : Mono (toCoind J n I f).hom := @mono_comp _ _ _ _ _ _ h₁ _ h₂
  exact (sheafToPresheaf J _).mono_of_mono_map this

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf
open Limits
variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) (n : ℕ)
  [J.HasSheafCompose (coindZMod.{u + 1} n)]

/-- The counit `forget (R F) ⟶ F` of coinduction, a kernel of multiplication by `n`. -/
noncomputable def coindCounit (F : Sheaf J AddCommGrpCat.{u + 1}) :
    (sheafCompose J (forget₂ _ AddCommGrpCat.{u + 1})).obj
      ((sheafCompose J (coindZMod.{u + 1} n)).obj F) ⟶ F :=
  ⟨Functor.whiskerLeft F.obj (forget₂CoindZModAdj.{u + 1} n).counit⟩

lemma zsmul_forget₂_eq_zero (M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) (x : M) :
    (n : ℤ) • x = 0 := by
  rw [← Int.cast_smul_eq_zsmul (ULift.{u + 1} (ZMod n))]
  have : ((n : ℤ) : ULift.{u + 1} (ZMod n)) = 0 := by ext; simp
  rw [this, zero_smul]

lemma counit_zsmul_eq_zero (A : AddCommGrpCat.{u + 1})
    (x : (forget₂ _ AddCommGrpCat.{u + 1}).obj ((coindZMod.{u + 1} n).obj A)) :
    (n : ℤ) • (forget₂CoindZModAdj.{u + 1} n).counit.app A x = 0 :=
  (map_zsmul (ConcreteCategory.hom ((forget₂CoindZModAdj.{u + 1} n).counit.app A))
    (n : ℤ) x).symm.trans
    ((congrArg _ (zsmul_forget₂_eq_zero n ((coindZMod.{u + 1} n).obj A) x)).trans (map_zero _))

lemma coindCounit_comp_zsmul (F : Sheaf J AddCommGrpCat.{u + 1}) :
    coindCounit J n F ≫ ((n : ℤ) • 𝟙 F) = 0 := by
  ext U x
  exact counit_zsmul_eq_zero n (F.obj.obj U) x

variable [HasSheafify J AddCommGrpCat.{u + 1}]

lemma shortExact_coindCounit (F : Sheaf J AddCommGrpCat.{u + 1}) [Injective F] (hn : n ≠ 0) :
    (ShortComplex.mk _ _ (coindCounit_comp_zsmul J n F)).ShortExact := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have hU (U : Cᵒᵖ) := forget₂CoindZModAdj_counit_shortExact.{u + 1} n (F.obj.obj U)
  have hmono : Mono (coindCounit J n F) := by
    have : Mono (coindCounit J n F).hom := by
      rw [NatTrans.mono_iff_mono_app]
      intro U
      exact (AddCommGrpCat.mono_iff_injective _).2 (hU U).1
    exact (sheafToPresheaf J _).mono_of_mono_map this
  have hepi := epi_zsmul_id_of_injective.{u + 1, u} J F hn'
  have hlim : IsLimit (KernelFork.ofι _ (coindCounit_comp_zsmul J n F)) := by
    apply isLimitOfReflects (sheafToPresheaf J AddCommGrpCat.{u + 1})
    refine evaluationJointlyReflectsLimits _ fun U ↦ ?_
    let S : ShortComplex AddCommGrpCat.{u + 1} :=
      ShortComplex.mk ((forget₂CoindZModAdj.{u + 1} n).counit.app (F.obj.obj U))
        ((n : ℤ) • 𝟙 _) (by
          ext x
          exact counit_zsmul_eq_zero n (F.obj.obj U) x)
    have hS : S.Exact := by
      rw [ShortComplex.ab_exact_iff]
      intro a ha
      exact (hU U).2 a (by simpa [S] using ha)
    have : Mono S.f := (AddCommGrpCat.mono_iff_injective _).2 (hU U).1
    exact (KernelFork.isLimitMapConeEquiv (KernelFork.ofι _ (coindCounit_comp_zsmul J n F))
      (sheafToPresheaf J AddCommGrpCat.{u + 1} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u + 1}).obj U)).symm
      hS.fIsKernel
  exact { exact := ShortComplex.exact_of_f_is_kernel _ hlim }

variable [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{u + 1})]

/-- **Injective sheaves of `ℤ/n`-modules are acyclic.** The underlying abelian sheaf of an
injective sheaf of `ℤ/n`-modules has no higher cohomology: it is a retract of the coinduced
sheaf `R F = Hom(ℤ/n, F)` of an injective abelian sheaf `F`, which is the `n`-torsion `F[n]`. -/
theorem subsingleton_H_forget₂_of_injective (hn : n ≠ 0)
    (I : Sheaf J (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) [Injective I] (q : ℕ) :
    Subsingleton (H ((sheafCompose J (forget₂ _ AddCommGrpCat.{u + 1})).obj I) (q + 1)) := by
  let G := (sheafCompose J (forget₂ _ AddCommGrpCat.{u + 1})).obj I
  let F := Injective.under G
  let g := toCoind J n I (Injective.ι G)
  have := mono_toCoind J n I (Injective.ι G)
  let p := Injective.factorThru (𝟙 I) g
  have hgp : g ≫ p = 𝟙 I := Injective.comp_factorThru _ _
  have hS := shortExact_coindCounit J n F hn
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have := mono_zsmul_id_constantSheaf.{u + 1, u} J hn'
  have := Abelian.Ext.subsingleton_of_shortExact_smul.{u + 1}
    (U := (constantSheaf J AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ)))
    (n : ℤ) (coindCounit_comp_zsmul J n F) hS q
  exact Abelian.Ext.subsingleton_of_retract ((sheafCompose J _).map g) ((sheafCompose J _).map p)
    (by rw [← Functor.map_comp, hgp, Functor.map_id]) (q + 1)

end CategoryTheory.Sheaf
