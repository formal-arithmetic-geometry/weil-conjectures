/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B9
-/
module

public import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Finite freeness of normalized free coefficient towers

Source: Bhatt--Scholze, Proposition 6.8.4(1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

namespace Padic

private theorem quotient_uniformizer_kernel {R : Type u} [CommRing R] [IsDomain R]
    (p : R) (hp : p ≠ 0) (n : ℕ)
    (x : R ⧸ Ideal.span ({p ^ (n + 2)} : Set R)) (hx : p • x = 0) :
    ∃ y, p ^ (n + 1) • y = x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hr : p * r ∈ Ideal.span ({p ^ (n + 2)} : Set R) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul] using hx
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hr
  have he : r = p ^ (n + 1) * s := by
    apply mul_left_cancel₀ hp
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hs
  refine ⟨Ideal.Quotient.mk _ s, ?_⟩
  simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul] using
    congrArg (Ideal.Quotient.mk (Ideal.span ({p ^ (n + 2)} : Set R))) he.symm

private theorem tower_uniformizer_injective {R : Type u} [CommRing R] [IsDomain R]
    (p : R) (hp : p ≠ 0) (F : ℕᵒᵖ ⥤ ModuleCat.{v} R)
    (hf : ∀ n : ℕ, ∃ r : ℕ, Nonempty
      (F.obj (op n) ≃ₗ[R] (Fin r → R ⧸ Ideal.span ({p ^ (n + 1)} : Set R))))
    (x : ModuleCat.sectionsSubmodule F) (hx : p • x = 0) : x = 0 := by
  have hkill (n : ℕ) (z : F.obj (op n)) : p ^ (n + 1) • z = 0 := by
    obtain ⟨r, ⟨e⟩⟩ := hf n
    apply e.injective
    ext i
    simp only [map_smul, map_zero, Pi.smul_apply, Pi.zero_apply]
    have hq : (Ideal.Quotient.mk (Ideal.span ({p ^ (n + 1)} : Set R)))
        (p ^ (n + 1)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self _)
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, hq, zero_mul]
  apply Subtype.ext
  funext j
  obtain ⟨r, ⟨e⟩⟩ := hf (j.unop + 1)
  have hx' : p • x.val (op (j.unop + 1)) = 0 :=
    congrArg (fun z : ModuleCat.sectionsSubmodule F ↦ z.val (op (j.unop + 1))) hx
  have he (i : Fin r) : p • e (x.val (op (j.unop + 1))) i = 0 := by
    have h := congrArg (fun z ↦ e z i) hx'
    simpa only [map_smul, Pi.smul_apply, map_zero, Pi.zero_apply] using h
  choose y hy using fun i ↦ quotient_uniformizer_kernel p hp j.unop _ (he i)
  have hxy : p ^ (j.unop + 1) • e.symm y = x.val (op (j.unop + 1)) := by
    apply e.injective
    ext i
    simpa only [map_smul, e.apply_symm_apply, Pi.smul_apply] using hy i
  have hn := x.property (homOfLE (Nat.le_succ j.unop)).op
  change F.map (homOfLE (Nat.le_succ j.unop)).op
    (x.val (op (j.unop + 1))) = x.val j at hn
  rw [← hn, ← hxy]
  change (F.map (homOfLE (Nat.le_succ j.unop)).op).hom
    (p ^ (j.unop + 1) • e.symm y) = 0
  rw [map_smul]
  exact hkill j.unop _

/-- A normalized tower of finite free uniformizer quotients has finite free inverse limit.
Source: Bhatt--Scholze, Proposition 6.8.4(1); Stacks Tags 09B8 and 031D.
(blueprint: lem-per-normalized-tower-finite-free).

Proof: the finite-module adic limit theorem makes the compatible-sections module finite.
If multiplication by the uniformizer kills a compatible family, its component at level
n+2 is divisible by the (n+1)st power, because that component lies in a free module over
the (n+2)nd quotient. Mapping to level n+1 kills it. Thus all components vanish.
Factor every nonzero scalar as a unit times a uniformizer power to deduce torsion-freeness.
A finite torsion-free module over the DVR is free, including the zero-rank case. -/
theorem normalized_tower_finite_free (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} (coefficientExtensionIntegers l E))
    (hf : ∀ n : ℕ, ∃ r : ℕ, Nonempty
      (F.obj (op n) ≃ₗ[coefficientExtensionIntegers l E]
        (Fin r → coefficientExtensionRing l E (n + 1))))
    (ht : ∀ n : ℕ,
      Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom ∧
      LinearMap.ker (F.map (homOfLE (Nat.le_succ n)).op).hom =
        coefficientExtensionIdeal l E (n + 1) •
          (⊤ : Submodule (coefficientExtensionIntegers l E) (F.obj (op (n + 1))))) :
    Module.Finite (coefficientExtensionIntegers l E) (ModuleCat.sectionsSubmodule F) ∧
      Module.Free (coefficientExtensionIntegers l E) (ModuleCat.sectionsSubmodule F) := by
  let R := coefficientExtensionIntegers l E
  let p := coefficientExtensionUniformizer l E
  let I := Ideal.span ({p} : Set R)
  have h := (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  let : IsLocalRing R := h.2.2.2.1
  let : IsDiscreteValuationRing R := h.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({p} : Set R) = coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hp : Irreducible p :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer p).mpr
      ((IsLocalRing.eq_maximalIdeal (R := R) h.2.2.2.2.1).symm.trans hgen.symm)
  have hfinite (n : ℕ) : Module.Finite R (F.obj (op n)) := by
    obtain ⟨r, ⟨e⟩⟩ := hf n
    exact Module.Finite.equiv e.symm
  have hkill (n : ℕ) : I ^ (n + 1) • (⊤ : Submodule R (F.obj (op n))) = ⊥ := by
    obtain ⟨r, ⟨e⟩⟩ := hf n
    apply le_antisymm _ bot_le
    refine Submodule.smul_le.mpr ?_
    intro a ha z _
    change a • z = 0
    apply e.injective
    ext i
    simp only [map_smul, map_zero, Pi.smul_apply, Pi.zero_apply]
    have hq : Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1)) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ha
    change Ideal.Quotient.mk (coefficientExtensionIdeal l E (n + 1)) a * e z i = 0
    rw [hq, zero_mul]
  let : Module.Finite R (ModuleCat.sectionsSubmodule F) :=
    (adicLimit_finite_modules l E F hfinite hkill ht).1
  have hf' : ∀ n : ℕ, ∃ r : ℕ, Nonempty
      (F.obj (op n) ≃ₗ[R] (Fin r → R ⧸ Ideal.span ({p ^ (n + 1)} : Set R))) := by
    intro n
    obtain ⟨r, ⟨e⟩⟩ := hf n
    have heq : coefficientExtensionIdeal l E (n + 1) =
        Ideal.span ({p ^ (n + 1)} : Set R) :=
      Ideal.span_singleton_pow p (n + 1)
    change F.obj (op n) ≃ₗ[R] (Fin r → R ⧸ coefficientExtensionIdeal l E (n + 1)) at e
    rw [heq] at e
    exact ⟨r, ⟨e⟩⟩
  have hpinj (x : ModuleCat.sectionsSubmodule F) (hx : p • x = 0) : x = 0 :=
    tower_uniformizer_injective p hp.ne_zero F hf' x hx
  let : Module.IsTorsionFree R (ModuleCat.sectionsSubmodule F) :=
    Module.IsTorsionFree.of_smul_eq_zero fun a x hx ↦ by
      by_cases ha : a = 0
      · exact Or.inl ha
      right
      obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hp
      rw [hv, mul_smul] at hx
      have hx' : p ^ n • x = 0 := (smul_eq_zero_iff_eq v).mp hx
      clear hx hv
      induction n with
      | zero => simpa only [pow_zero, one_smul] using hx'
      | succ n ih =>
        apply ih
        apply hpinj
        simpa only [pow_succ', mul_smul] using hx'
  exact ⟨inferInstance, inferInstance⟩

/-- The categorical limit is the module of compatible families.
Source: the universal property of a limit of modules.
(blueprint: lem-per-normalized-tower-finite-free). -/
def towerLimitEquivSections {R : Type u} [CommRing R]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) :
    (CategoryTheory.Limits.limit F : ModuleCat.{v} R) ≃ₗ[R] ModuleCat.sectionsSubmodule F := by
  let S := ModuleCat.sectionsSubmodule F
  let c : Cone F :=
    { pt := ModuleCat.of R S
      π :=
        { app := fun j ↦ ModuleCat.ofHom ((LinearMap.proj j).comp S.subtype)
          naturality := fun i j f ↦ by
            ext x
            exact (x.property f).symm } }
  let hc : IsLimit c :=
    { lift := fun s ↦ ModuleCat.ofHom
        { toFun := fun x ↦ ⟨fun j ↦ s.π.app j x, fun {i j} f ↦ by
            exact ConcreteCategory.congr_hom (s.w f) x⟩
          map_add' := fun x y ↦ by ext j; exact map_add (s.π.app j).hom x y
          map_smul' := fun a x ↦ by ext j; exact map_smul (s.π.app j).hom a x }
      fac := fun s j ↦ by ext x; rfl
      uniq := fun s m hm ↦ by
        ext x j
        exact ConcreteCategory.congr_hom (hm j) x }
  exact ((limit.isLimit F).conePointUniqueUpToIso hc).toLinearEquiv

/-- Finite freeness in the categorical limit presentation.
Source: Bhatt--Scholze, Proposition 6.8.4(1).
(blueprint: lem-per-normalized-tower-finite-free).
Proof: transport the compatible-sections result through its limit universal property. -/
theorem normalized_tower_limit_finite_free (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} (coefficientExtensionIntegers l E))
    (hf : ∀ n : ℕ, ∃ r : ℕ, Nonempty
      (F.obj (op n) ≃ₗ[coefficientExtensionIntegers l E]
        (Fin r → coefficientExtensionRing l E (n + 1))))
    (ht : ∀ n : ℕ,
      Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom ∧
      LinearMap.ker (F.map (homOfLE (Nat.le_succ n)).op).hom =
        coefficientExtensionIdeal l E (n + 1) •
          (⊤ : Submodule (coefficientExtensionIntegers l E) (F.obj (op (n + 1))))) :
    Module.Finite (coefficientExtensionIntegers l E) (CategoryTheory.Limits.limit F :
        ModuleCat.{v} (coefficientExtensionIntegers l E)) ∧
      Module.Free (coefficientExtensionIntegers l E) (CategoryTheory.Limits.limit F :
        ModuleCat.{v} (coefficientExtensionIntegers l E)) := by
  obtain ⟨hfin, hfree⟩ := normalized_tower_finite_free l E F hf ht
  let : Module.Finite (coefficientExtensionIntegers l E)
      (ModuleCat.sectionsSubmodule F) := hfin
  let : Module.Free (coefficientExtensionIntegers l E)
      (ModuleCat.sectionsSubmodule F) := hfree
  exact ⟨Module.Finite.equiv (towerLimitEquivSections F).symm,
    Module.Free.of_equiv (towerLimitEquivSections F).symm⟩

end Padic
