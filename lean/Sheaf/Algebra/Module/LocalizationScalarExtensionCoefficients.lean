/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-! # Coefficient extension and ordinary module localization

Source: Stacks, algebra.tex, Tags 07JZ, 00DK and 00D2.
(blueprint: lem-sfb-localization-scalar-extension-coefficients)
-/

@[expose] public section

universe u v w t
open TensorProduct
namespace LocalizedModule

/-- Ordinary localization commutes with extension of the coefficient ring.

Source: Stacks, algebra.tex, Tags 07JZ (module fractions), 00DK (localization as
a tensor product) and 00D2 (tensor associativity); the ungraded part of constructions.tex,
Tag 01N2, on standard opens.
(blueprint: lem-sfb-localization-scalar-extension-coefficients)

Proof: Regard N = S ⊗_R M as an A-module via the scalar-extended action. Tensoring
M → M_f with S is a localization at the powers of f, by
IsLocalizedModule.rTensor, after commuting the factors. The map N → N_(1⊗f)
is also a localization at the powers of f after restricting scalars along
A → S ⊗_R A, by IsLocalizedModule.restrictScalars_powers. Uniqueness of module
localization gives an A-linear equivalence. It sends s⊗(x/1) to (s⊗x)/1.
Multiply by f^m and use injectivity of multiplication by the denominator to
obtain the formula on arbitrary fractions. This formula and induction on tensors
show S-linearity, so the equivalence upgrades to an S-linear equivalence. -/
theorem exists_localization_scalarExtension_coefficients_equiv
    {R : Type u} {S : Type v} {A : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing A] [AddCommGroup M]
    [Algebra R S] [Algebra R A] [Module R M] [Module A M] [IsScalarTower R A M]
    (f : A) :
    let ρ : (S ⊗[R] A) →ₐ[S] Module.End S (S ⊗[R] M) :=
      AlgHom.liftEquiv R S A _
        ((Module.End.baseChangeHom R S M).comp (Algebra.lsmul R R M))
    letI : Module (S ⊗[R] A) (S ⊗[R] M) := Module.compHom _ ρ.toRingHom
    letI : IsScalarTower S (S ⊗[R] A) (S ⊗[R] M) :=
      IsScalarTower.of_algebraMap_smul
        (fun s x ↦ congrArg (fun g : Module.End S (S ⊗[R] M) ↦ g x) (ρ.commutes s))
    ∃ e : (S ⊗[R] LocalizedModule.Away f M) ≃ₗ[S]
      LocalizedModule.Away (1 ⊗ₜ[R] f : S ⊗[R] A) (S ⊗[R] M),
      ∀ (s : S) (m : ℕ) (x : M),
        e (s ⊗ₜ[R] mk x (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)) =
          mk (s ⊗ₜ[R] x)
            (⟨(1 ⊗ₜ[R] f : S ⊗[R] A) ^ m, ⟨m, rfl⟩⟩ :
              Submonoid.powers (1 ⊗ₜ[R] f : S ⊗[R] A)) := by
  dsimp only
  let ρ : (S ⊗[R] A) →ₐ[S] Module.End S (S ⊗[R] M) :=
    AlgHom.liftEquiv R S A _
      ((Module.End.baseChangeHom R S M).comp (Algebra.lsmul R R M))
  let : Module (S ⊗[R] A) (S ⊗[R] M) := Module.compHom _ ρ.toRingHom
  let : IsScalarTower S (S ⊗[R] A) (S ⊗[R] M) :=
    IsScalarTower.of_algebraMap_smul
      (fun s x ↦ congrArg (fun g : Module.End S (S ⊗[R] M) ↦ g x) (ρ.commutes s))
  let : IsScalarTower R (S ⊗[R] A) (S ⊗[R] M) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      rw [IsScalarTower.algebraMap_apply R S (S ⊗[R] A), algebraMap_smul,
        algebraMap_smul]
  let : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let : Module A (S ⊗[R] M) := Module.compHom _ (algebraMap A (S ⊗[R] A))
  let : IsScalarTower A (S ⊗[R] A) (S ⊗[R] M) :=
    IsScalarTower.of_compHom A (S ⊗[R] A) (S ⊗[R] M)
  let : IsScalarTower R A (S ⊗[R] M) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦ by
      change algebraMap A (S ⊗[R] A) (algebraMap R A r) • x = r • x
      rw [← IsScalarTower.algebraMap_apply R A (S ⊗[R] A),
        IsScalarTower.algebraMap_apply R S (S ⊗[R] A), algebraMap_smul, algebraMap_smul]
  have hact (a : A) (s : S) (x : M) : a • (s ⊗ₜ[R] x) = s ⊗ₜ[R] (a • x) := by
    change (ρ (1 ⊗ₜ[R] a)) (s ⊗ₜ[R] x) = _
    simp only [ρ, AlgHom.liftEquiv_tmul, one_smul, AlgHom.comp_apply]
    exact LinearMap.baseChange_tmul (A := S) (f := Algebra.lsmul R R M a) s x
  let c : (M ⊗[R] S) ≃ₗ[A] S ⊗[R] M :=
    { TensorProduct.comm R M S with
      map_smul' := fun a x ↦ by
        change (TensorProduct.comm R M S) (a • x) = a • (TensorProduct.comm R M S) x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul m s => simp only [smul_tmul', comm_tmul, hact]
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
  let l := mkLinearMap (Submonoid.powers f) M
  let t := AlgebraTensorModule.rTensor R S l
  let k := (mkLinearMap (Submonoid.powers (1 ⊗ₜ[R] f : S ⊗[R] A))
    (S ⊗[R] M)).restrictScalars A
  have : IsLocalizedModule (Submonoid.powers (algebraMap A (S ⊗[R] A) f))
      (mkLinearMap (Submonoid.powers (1 ⊗ₜ[R] f : S ⊗[R] A)) (S ⊗[R] M)) := by
    simpa only [Algebra.TensorProduct.right_algebraMap_apply] using
      (inferInstance : IsLocalizedModule (Submonoid.powers (1 ⊗ₜ[R] f : S ⊗[R] A))
        (mkLinearMap (Submonoid.powers (1 ⊗ₜ[R] f : S ⊗[R] A)) (S ⊗[R] M)))
  have : IsLocalizedModule (Submonoid.powers f) k :=
    IsLocalizedModule.restrictScalars_powers f _
  have : IsLocalizedModule (Submonoid.powers f) (k.comp c.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right _ _ c
  let E := IsLocalizedModule.linearEquiv (Submonoid.powers f) t (k.comp c.toLinearMap)
  have hE (x : M ⊗[R] S) : E (t x) = k (c x) :=
    IsLocalizedModule.linearEquiv_apply _ _ _ x
  have hfrac (s : S) (m : ℕ) (x : M) :
      E (mk x (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) ⊗ₜ[R] s) =
        mk (s ⊗ₜ[R] x)
          (⟨(1 ⊗ₜ[R] f : S ⊗[R] A) ^ m, ⟨m, rfl⟩⟩ :
            Submonoid.powers (1 ⊗ₜ[R] f : S ⊗[R] A)) := by
    apply IsLocalizedModule.smul_injective k (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)
    change f ^ m • E _ = f ^ m • _
    rw [← E.map_smul, smul_tmul']
    have hc : f ^ m • mk x (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) = mk x 1 := by
      rw [smul'_mk]
      exact mk_cancel (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) x
    rw [hc]
    have hb := hE (x ⊗ₜ[R] s)
    change E (mk x 1 ⊗ₜ[R] s) = mk (s ⊗ₜ[R] x) 1 at hb
    rw [hb]
    rw [← algebraMap_smul (S ⊗[R] A) (f ^ m), map_pow,
      Algebra.TensorProduct.right_algebraMap_apply, smul'_mk]
    exact (mk_cancel
      (⟨(1 ⊗ₜ[R] f : S ⊗[R] A) ^ m, ⟨m, rfl⟩⟩ :
        Submonoid.powers (1 ⊗ₜ[R] f : S ⊗[R] A)) (s ⊗ₜ[R] x)).symm
  let eR : (S ⊗[R] LocalizedModule.Away f M) ≃ₗ[R]
      LocalizedModule.Away (1 ⊗ₜ[R] f : S ⊗[R] A) (S ⊗[R] M) :=
    (TensorProduct.comm R S (LocalizedModule.Away f M)).trans (E.restrictScalars R)
  have hS (a : S) (z : S ⊗[R] LocalizedModule.Away f M) : eR (a • z) = a • eR z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s z =>
      induction z using LocalizedModule.induction_on with
      | h x t =>
        obtain ⟨m, hm⟩ := t.property
        have ht : t = (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext hm.symm
        subst t
        rw [smul_tmul']
        change E (mk x _ ⊗ₜ[R] (a * s)) = a • E (mk x _ ⊗ₜ[R] s)
        rw [hfrac, hfrac, smul'_mk, smul_tmul', smul_eq_mul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  let e : (S ⊗[R] LocalizedModule.Away f M) ≃ₗ[S]
      LocalizedModule.Away (1 ⊗ₜ[R] f : S ⊗[R] A) (S ⊗[R] M) :=
    { eR with map_smul' := hS }
  refine ⟨e, ?_⟩
  intro s m x
  exact hfrac s m x

end LocalizedModule
