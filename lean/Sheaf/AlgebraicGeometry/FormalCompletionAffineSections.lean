/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.RingTheory.AdicCompletion.Basic

import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.Algebra.Module.AdicCompletionStableRanges

/-! # Affine sections of a module completion

Source: Stacks Project, Tags 01I8 and 01IC, and the quotient-limit definition of completion.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped TensorProduct in
/-- Affine exactness identifies the actual quotient projection with the module quotient.
Source: Stacks Project, Tags 01I8 and 01IC. The affine tensor comparison computes the
multiplication range on pure tensors. The image comparison identifies the product
inclusion with that range; affine exactness and the first isomorphism theorem finish. -/
private theorem quotient_sections_iso {Y : Scheme.{u}}
    (J : Y.IdealSheafData) (H : Y.Modules) [H.IsQuasicoherent]
    (U : Y.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    let R := Γ(Y, U)
    let I := J.ideal ⟨U, hU⟩
    let M := Γ(H, U)
    let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
    ∃ q : ModuleCat.of R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) ≅
        E.obj (formalModuleQuotient J (n + 1) H),
      ModuleCat.ofHom (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule R M))) ≫ q.hom =
        E.map (formalModuleQuotientπ J (n + 1) H) := by
  let V : Y.affineOpens := ⟨U, hU⟩
  let R := Γ(Y, U)
  let I := J.ideal V
  let M := Γ(H, U)
  let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  let a := Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (n + 1)).2 H
  let K := (Scheme.idealSheafPower J.toModulesι (n + 1)).1
  let i := (Scheme.idealSheafPower J.toModulesι (n + 1)).2
  have : K.IsQuasicoherent :=
    (Scheme.Modules.ideal_times_quasiCoherent_affine_sections J H).2.2.1
      (n + 1) (Nat.succ_pos n)
  let : MonoidalCategory Y.Modules := SheafOfModules.monoidalCategory Y.sheaf
  let b := MonoidalCategoryStruct.whiskerRight i H ≫
    (MonoidalCategoryStruct.leftUnitor H).hom
  have := (Scheme.Modules.quasiCoherent_tensor_product_affine_sections K H).1
  have hqc : (Scheme.idealModuleProduct i H).IsQuasicoherent := by
    have him := (Scheme.Modules.quasiCoherent_cokernel_image b).2.2.2.2.2.2.2.1
    exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
      (Abelian.imageIsoImage b) him
  have hpow := ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections J H).2.2.2.1
    V).2.2.2 (n + 1) (Nat.succ_pos n)
  have heq : (LinearMap.range
      ((Scheme.idealSheafPower J.toModulesι (n + 1)).2.val.app (op U)).hom :
        Ideal R) = I ^ (n + 1) := SetLike.coe_injective hpow
  have ht := (Scheme.Modules.quasiCoherent_tensor_product_affine_sections K H).2 U hU
  have hb (s : Γ(K, U)) (t : M) :
      b.app U (Scheme.Modules.tensorSectionsMap K H U (s ⊗ₜ t)) =
        (show R from i.app U s) • t := by
    rw [Scheme.Modules.tensorSectionsMap_tmul]
    change (MonoidalCategoryStruct.leftUnitor H).hom.app U
      ((MonoidalCategoryStruct.whiskerRight i H).app U
        (Scheme.Modules.tmulSection s t)) = _
    rw [Scheme.Modules.whiskerRight_app_tmulSection,
      Scheme.Modules.leftUnitor_hom_app_tmulSection']
    rfl
  have hrb : LinearMap.range (b.val.app (op U)).hom =
      I ^ (n + 1) • (⊤ : Submodule R M) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := ht.2 z
      induction w using TensorProduct.induction_on with
      | zero => simp only [map_zero]; exact Submodule.zero_mem _
      | tmul s t =>
        change b.app U (Scheme.Modules.tensorSectionsMap K H U (s ⊗ₜ t)) ∈ _
        rw [hb]
        exact Submodule.smul_mem_smul (heq ▸ ⟨s, rfl⟩) (Submodule.mem_top)
      | add x y hx hy =>
        simp only [map_add]
        exact Submodule.add_mem _ hx hy
    · apply Submodule.smul_le.mpr
      intro r hr t _
      obtain ⟨s, rfl⟩ := (heq.symm ▸ hr)
      exact ⟨Scheme.Modules.tensorSectionsMap K H U (s ⊗ₜ t), hb s t⟩
  have him := (Scheme.Modules.quasiCoherent_cokernel_image b).2.2.2.2.2.2.2.2 V
  have hi : Set.range (a.app U) = Set.range ((Abelian.image.ι b).app U) := by
    let e := Abelian.imageIsoImage b
    ext s
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨e.inv.app U t, ?_⟩
      have h : e.inv ≫ Abelian.image.ι b = image.ι b := by
        calc
          _ = e.inv ≫ e.hom ≫ image.ι b :=
            congrArg (fun f ↦ e.inv ≫ f)
              (Abelian.imageIsoImage_hom_comp_image_ι b).symm
          _ = _ := by simp
      exact congrArg (fun f ↦ f.app U t) h
    · rintro ⟨t, rfl⟩
      refine ⟨e.hom.app U t, ?_⟩
      exact congrArg (fun f ↦ f.app U t) (Abelian.imageIsoImage_hom_comp_image_ι b)
  have hr : LinearMap.range (a.val.app (op U)).hom =
      I ^ (n + 1) • (⊤ : Submodule R M) := by
    apply SetLike.coe_injective
    change Set.range (a.app U) = _
    rw [hi, him.1]
    exact congrArg (fun P : Submodule R M ↦ (P : Set M)) hrb
  have ha := (Scheme.Modules.quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.2 V
  let ρ : M →ₗ[R] E.obj (formalModuleQuotient J (n + 1) H) :=
    (E.map (formalModuleQuotientπ J (n + 1) H)).hom
  have hsurj : Function.Surjective ρ := ha.2.1
  have hker : LinearMap.ker ρ = I ^ (n + 1) • (⊤ : Submodule R M) := by
    change LinearMap.ker ((cokernel.π a).val.app (op U)).hom = _
    rw [ha.2.2.1]
    exact hr
  let e := (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (ρ.quotKerEquivOfSurjective hsurj)
  refine ⟨e.toModuleIso, ?_⟩
  ext x
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine quotient identifications give a canonical completion isomorphism.
Source: Stacks Project, Tags 01I8 and 01IC; Cohomology of Schemes, Lemma 088B.
(blueprint: lem-weil-pbc-formal-completion-affine-sections)

Proof: Set A = Gamma(Y,U), I = J(U), and M = Gamma(U,H). On an affine open,
quasi-coherent sheaves are modules, and affine sections are exact. The range of the
inclusion of J^(n+1)H is I^(n+1)M: the ideal power formula and tensor section formula
identify multiplication, and exactness identifies its image. Thus the actual quotient
projection is surjective with kernel I^(n+1)M. Its first isomorphism theorem gives q_n,
with the displayed projection equation. Cancel the surjective quotient projections to
check that q_n commutes with all transitions. Evaluation preserves limits, so these
compatible isomorphisms identify the evaluated sheaf limit with the limit of M/I^(n+1)M.
This limit is the adic completion: the omitted exponent-zero quotient is zero, and
inserting its unique zero coordinate gives the inverse identification. Its projections
are exactly AdicCompletion.eval at n+1, which proves the final equation.
For the zero ideal the systems are constant; for the unit ideal they are zero. The zero
module and empty affine open give zero modules throughout; no nonzero-ring assumption
is needed. No proper morphism or comparison map is used in this statement.
-/
theorem formalCompletion_affine_sections {Y : Scheme.{u}}
    (J : Y.IdealSheafData) (H : Y.Modules) [H.IsQuasicoherent]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    let R := Γ(Y, U)
    let I := J.ideal ⟨U, hU⟩
    let M := Γ(H, U)
    let S := formalCompletionSystem J H
    let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
    ∃ q : ∀ n : ℕ,
        ModuleCat.of R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) ≅
          E.obj (S.obj (op n)),
      (∀ n : ℕ, ModuleCat.ofHom
        (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule R M))) ≫ (q n).hom =
          E.map (formalModuleQuotientπ J (n + 1) H)) ∧
      ∃ e : ModuleCat.of R (AdicCompletion I M) ≅ E.obj (limit S),
        ∀ n : ℕ, e.hom ≫ E.map (limit.π S (op n)) =
          ModuleCat.ofHom (AdicCompletion.eval I M (n + 1)) ≫ (q n).hom := by
  classical
  let R := Γ(Y, U)
  let I := J.ideal ⟨U, hU⟩
  let M := Γ(H, U)
  let S := formalCompletionSystem J H
  let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  choose q hq using fun n ↦ quotient_sections_iso J H U hU n
  let T := S ⋙ E
  let ρ (n : ℕ) : M →ₗ[R] T.obj (op n) :=
    (E.map (formalModuleQuotientπ J (n + 1) H)).hom
  let θ (n : ℕ) : (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) →ₗ[R]
      T.obj (op n) := (q n).hom.hom
  have hθ (n : ℕ) : (θ n).comp (Submodule.mkQ (I ^ (n + 1) • ⊤)) = ρ n := by
    exact congrArg ModuleCat.Hom.hom (hq n)
  have hqval (n : ℕ) (y : M) :
      (q n).hom ((I ^ (n + 1) • (⊤ : Submodule R M)).mkQ y) = ρ n y :=
    LinearMap.congr_fun (hθ n) y
  have htrans (n m : ℕ) (h : n ≤ m) :
      (T.map (homOfLE h).op).hom.comp (θ m) =
        (θ n).comp (AdicCompletion.transitionMap I M (Nat.succ_le_succ h)) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ_surjective x
    change (T.map (homOfLE h).op) ((q m).hom
      ((I ^ (m + 1) • (⊤ : Submodule R M)).mkQ y)) =
        (q n).hom ((I ^ (n + 1) • (⊤ : Submodule R M)).mkQ y)
    rw [hqval, hqval]
    change (E.map (formalModuleQuotientπ J (m + 1) H) ≫
      E.map (formalModuleQuotientMap J (𝟙 H) (Nat.succ_le_succ h))) y = _
    rw [← E.map_comp]
    simp only [formalModuleQuotientMap, formalModuleQuotientπ, cokernel.π_desc,
      Category.id_comp]
    rfl
  have hker (n : ℕ) : LinearMap.ker (ρ (n + 0)) ≤
      I ^ (n + 1) • (⊤ : Submodule R M) := by
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply (q n).toLinearEquiv.injective
    change (θ n) ((I ^ (n + 1) • (⊤ : Submodule R M)).mkQ x) = (q n).hom 0
    rw [map_zero]
    exact (LinearMap.congr_fun (hθ n) x).trans hx
  have hrange (n : ℕ) :
      Set.range (T.map (homOfLE (Nat.le_add_right n 0)).op).hom = Set.range (ρ n) := by
    have hs : Function.Surjective (ρ n) := by
      rw [← hθ n]
      exact (q n).toLinearEquiv.surjective.comp (Submodule.mkQ_surjective _)
    rw [Set.range_eq_univ.mpr hs]
    have hi : (homOfLE (Nat.le_add_right n 0)).op = 𝟙 (op n) := Subsingleton.elim _ _
    rw [hi]
    exact (congrArg (fun k ↦ Set.range k.hom) (T.map_id (op n))).trans
      (Set.range_eq_univ.mpr Function.surjective_id)
  obtain ⟨e₀, he₀⟩ := adicCompletion_iso_of_stable_ranges I (ModuleCat.of R M)
    T ρ θ hθ htrans 0 hker hrange
  let e := e₀ ≪≫ (preservesLimitIso E S).symm
  refine ⟨q, hq, e, ?_⟩
  intro n
  dsimp only [e, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, preservesLimitIso_inv_π, he₀]
  rfl

end AlgebraicGeometry
