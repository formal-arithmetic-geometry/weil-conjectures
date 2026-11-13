/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.IdealPowerTorsionFreeSectionCarrier
import WeilConjectures.AlgebraicGeometry.IdealDataRecursivePowerComparison
import WeilConjectures.AlgebraicGeometry.IdealPowerComplement
import WeilConjectures.AlgebraicGeometry.IdealPowerTorsionFreeSectionLifting
import WeilConjectures.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import WeilConjectures.AlgebraicGeometry.Modules.IdealSheafFiniteType

/-! # Extending a quasi-coherent section from an ideal power

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

noncomputable local instance {X : Scheme.{u}} (F : X.Modules) {V W : X.Opens} (h : V ≤ W) :
    HSMul ((SheafOfModules.unit X.ringCatSheaf).val.obj (op V))
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (homOfLE h).op).hom).obj
        (F.val.obj (op V))) (F.val.obj (op V)) where
  hSMul := @SMul.smul Γ(X, V) Γ(F, V) inferInstance

noncomputable local instance {X : Scheme.{u}} (F : X.Modules) {V W : X.Opens} (h : V ≤ W) :
    HSMul Γ(SheafOfModules.unit X.ringCatSheaf, V)
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (homOfLE h).op).hom).obj
        (F.val.obj (op V))) (F.val.obj (op V)) where
  hSMul := @SMul.smul Γ(X, V) Γ(F, V) inferInstance

private theorem power_factor {X : Scheme.{u}} {P : X.Modules}
    (ι : P ⟶ SheafOfModules.unit X.ringCatSheaf) {n m : ℕ} (h : n ≤ m) :
    ∃ r : (idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1,
      r ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2 := by
  have hs (k : ℕ) :
      ∃ r : (idealSheafPower ι (k + 1)).1 ⟶ (idealSheafPower ι k).1,
        r ≫ (idealSheafPower ι k).2 = (idealSheafPower ι (k + 1)).2 := by
    cases k with
    | zero => exact ⟨ι, Category.comp_id _⟩
    | succ k => exact ⟨idealModuleProductι ι _, rfl⟩
  induction h with
  | refl => exact ⟨𝟙 _, Category.id_comp _⟩
  | @step m h ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨t, ht⟩ := hs m
    exact ⟨t ≫ r, by rw [Category.assoc, hr, ht]⟩

set_option backward.isDefEq.respectTransparency false in
/-- A section on the complement of an ideal support extends from an ideal power. -/
theorem quasicoherent_open_section_ideal_extension
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (E : X.Modules) [E.IsQuasicoherent] (U : X.Opens)
    (hI : (I.support : Set X) = (U : Set X)ᶜ) (s : E.val.obj (op U)) :
    ∃ (n : ℕ) (α : (I ^ n).toModules ⟶ E),
      ∀ (W : X.Opens) (h : W ≤ U) (a : (I ^ n).toModules.val.obj (op W)),
        α.val.app (op W) a =
          (I ^ n).toModulesι.val.app (op W) a • E.val.map (homOfLE h).op s := by
  classical
  have hqc : I.toModules.IsQuasicoherent := by
    simpa using (idealData_recursive_power_comparison I 1).1
  have : I.toModules.IsQuasicoherent := hqc
  have : I.toModules.IsFiniteType := I.isFiniteType_toModules I.ofFiniteType_of_isLocallyNoetherian
  obtain ⟨V, hV, hbij⟩ := ideal_power_complement I.toModulesι
  have hVU : V = U := by
    ext x
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (⊤ : X.Opens) from trivial)
        (⊤ : X.Opens).isOpen
    have hh := (quasi_coherent_ideal_zero_set_affine X I).2.1 ⟨W, hW⟩ ⟨x, hxW⟩
    change x ∈ V ↔ x ∈ U
    rw [hV x, hh]
    have hp := Set.ext_iff.mp (hW.fromSpec_preimage_zeroLocus (I.ideal ⟨W, hW⟩))
      (hW.primeIdealOf ⟨x, hxW⟩)
    change (hW.fromSpec (hW.primeIdealOf ⟨x, hxW⟩) ∈
      X.zeroLocus (U := W) (I.ideal ⟨W, hW⟩ : Set Γ(X, W))) ↔
      I.ideal ⟨W, hW⟩ ≤ (hW.primeIdealOf ⟨x, hxW⟩).asIdeal at hp
    rw [hW.fromSpec_primeIdealOf] at hp
    rw [← hp, ← I.mem_support_iff_of_mem (U := ⟨W, hW⟩) hxW]
    change x ∉ (I.support : Set X) ↔ x ∈ (U : Set X)
    rw [hI]
    simp
  subst V
  let one : ∀ n : ℕ, Γ((idealSheafPower I.toModulesι n).1, U) :=
    fun n ↦ ((hbij n U le_rfl).2 (1 : Γ(X, U))).choose
  have hone (n : ℕ) :
      (idealSheafPower I.toModulesι n).2.app U (one n) = (1 : Γ(X, U)) :=
    ((hbij n U le_rfl).2 (1 : Γ(X, U))).choose_spec
  let r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower I.toModulesι m).1 ⟶ (idealSheafPower I.toModulesι n).1) :=
    fun _ _ h ↦ (power_factor I.toModulesι h).choose
  have hr (n m : ℕ) (h : n ≤ m) :
      r n m h ≫ (idealSheafPower I.toModulesι n).2 =
        (idealSheafPower I.toModulesι m).2 := (power_factor I.toModulesι h).choose_spec
  obtain ⟨G, g, t, hG, _, ht, htf⟩ :=
    exists_idealPower_torsionFree_section_carrier I E U hI s
  have : G.IsQuasicoherent := hG
  obtain ⟨n, ψ, hψ⟩ := ideal_power_torsionFree_section_lifting I.toModulesι G U one r
    hV hone hr htf t
  obtain ⟨e, he⟩ := (idealData_recursive_power_comparison I n).2
  refine ⟨n, e.hom ≫ ψ ≫ g, ?_⟩
  intro W h b
  let z := G.val.map (homOfLE h).op t
  let o := (idealSheafPower I.toModulesι n).1.val.map (homOfLE h).op (one n)
  have ho : (idealSheafPower I.toModulesι n).2.app W o = (1 : Γ(X, W)) := by
    have hh := PresheafOfModules.naturality_apply
      (idealSheafPower I.toModulesι n).2.val (homOfLE h).op (one n)
    change _ = X.presheaf.map (homOfLE h).op _ at hh
    change (idealSheafPower I.toModulesι n).2.val.app (op W)
      ((idealSheafPower I.toModulesι n).1.val.map (homOfLE h).op (one n)) = _
    rw [hh]
    change X.presheaf.map (homOfLE h).op
      ((idealSheafPower I.toModulesι n).2.app U (one n)) = _
    rw [hone]
    exact map_one _
  have hz : ψ.app W o = z := by
    exact (PresheafOfModules.naturality_apply ψ.val (homOfLE h).op (one n)).trans
      (congrArg (G.val.map (homOfLE h).op) hψ)
  have hb : e.hom.app W b = ((I ^ n).toModulesι.app W b : Γ(X, W)) • o := by
    apply (hbij n W h).1
    rw [Hom.app_smul, ho]
    have hh := congrArg (fun f ↦ f.app W b) he
    simpa only [Hom.comp_app, ConcreteCategory.comp_apply, smul_eq_mul, mul_one]
      using hh
  change g.app W (ψ.app W (e.hom.app W b)) = _
  rw [hb, Hom.app_smul, hz, Hom.app_smul]
  have hh := PresheafOfModules.naturality_apply g.val (homOfLE h).op t
  change _ • g.val.app (op W) (G.val.map (homOfLE h).op t) = _
  rw [hh, ht]
  rfl

end AlgebraicGeometry.Scheme.Modules
