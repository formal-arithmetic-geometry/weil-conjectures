/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.RingTheory.Invariant.Reynolds
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Invariants of a base change and of an integral closure

Let `Γ` be a finite group acting on an `R`-algebra `R'` by `R`-algebra automorphisms, with
`R'^Γ = R` and `|Γ|` invertible in `R`, and let `M` be an `R`-algebra. Let `Γ` act on
`R' ⊗[R] M` through the first factor (`Algebra.IsInvariant.tensorAction`). Then:

* the invariants of `R' ⊗[R] M` are the elements `1 ⊗ m`
  (`Algebra.IsInvariant.mem_range_includeRight_of_forall_smul_eq`), by averaging over `Γ`;
* `Γ` acts on the integral closure `T'` of `R'` in `R' ⊗[R] M`
  (`Algebra.IsInvariant.integralClosureAction`), and if `M → R' ⊗[R] M` is injective then the
  invariants of `T'` are the elements `1 ⊗ t` for `t` in the integral closure of `R` in `M`
  (`Algebra.IsInvariant.exists_eq_includeRight_of_forall_smul_eq_integralClosure`).

This is used to identify the invariants of the normalization after a tame Kummer base change in
the trait case of blueprint `sbc-thm-spreading-finite-etale-galois` ([Stacks 0EYJ]).
-/

@[expose] public section

open TensorProduct

namespace Algebra.IsInvariant

variable {R R' M : Type*} [CommRing R] [CommRing R'] [Algebra R R'] [CommRing M] [Algebra R M]
  (Γ : Type*) [Group Γ] [MulSemiringAction Γ R'] [SMulCommClass Γ R R']

/-- The action of `Γ` on `R' ⊗[R] M` through the first factor, as a group homomorphism. -/
noncomputable def tensorAlgAut : Γ →* (R' ⊗[R] M ≃ₐ[R] R' ⊗[R] M) where
  toFun g := Algebra.TensorProduct.congr (MulSemiringAction.toAlgEquiv R R' g) AlgEquiv.refl
  map_one' := by
    refine AlgEquiv.coe_algHom_injective (Algebra.TensorProduct.ext' fun a m ↦ ?_)
    simp
  map_mul' g h := by
    refine AlgEquiv.coe_algHom_injective (Algebra.TensorProduct.ext' fun a m ↦ ?_)
    simp [mul_smul]

/-- The action of `Γ` on `R' ⊗[R] M` through the first factor. -/
@[instance_reducible]
noncomputable def tensorAction : MulSemiringAction Γ (R' ⊗[R] M) :=
  MulSemiringAction.compHom _ (tensorAlgAut (R := R) (R' := R') (M := M) Γ)

variable {Γ}

lemma tensorAction_smul_def (g : Γ) (x : R' ⊗[R] M) :
    letI := tensorAction (R := R) (R' := R') (M := M) Γ
    g • x = tensorAlgAut (R := R) (R' := R') (M := M) Γ g x :=
  rfl

lemma tensorAction_smul_tmul (g : Γ) (a : R') (m : M) :
    letI := tensorAction (R := R) (R' := R') (M := M) Γ
    g • (a ⊗ₜ[R] m) = (g • a) ⊗ₜ[R] m :=
  rfl

lemma tensorAction_smul_algebraMap (g : Γ) (a : R') :
    letI := tensorAction (R := R) (R' := R') (M := M) Γ
    g • algebraMap R' (R' ⊗[R] M) a = algebraMap R' (R' ⊗[R] M) (g • a) :=
  rfl

variable [Fintype Γ] [Algebra.IsInvariant R R' Γ]

/-- **Invariants of a base change.** If `R'^Γ = R` and `|Γ|` is invertible, the `Γ`-invariant
elements of `R' ⊗[R] M` are the elements `1 ⊗ m`. -/
theorem mem_range_includeRight_of_forall_smul_eq (hΓ : IsUnit (Fintype.card Γ : R))
    (x : R' ⊗[R] M)
    (hx : letI := tensorAction (R := R) (R' := R') (M := M) Γ; ∀ g : Γ, g • x = x) :
    x ∈ Set.range (Algebra.TensorProduct.includeRight : M →ₐ[R] R' ⊗[R] M) := by
  letI := tensorAction (R := R) (R' := R') (M := M) Γ
  let N : Submodule R (R' ⊗[R] M) :=
    LinearMap.range (Algebra.TensorProduct.includeRight : M →ₐ[R] R' ⊗[R] M).toLinearMap
  have key (y : R' ⊗[R] M) : ∑ g : Γ, g • y ∈ N := by
    induction y with
    | zero => simp
    | add y z hy hz =>
      simp_rw [smul_add, Finset.sum_add_distrib]
      exact N.add_mem hy hz
    | tmul a m =>
      obtain ⟨b, hb⟩ := exists_algebraMap_eq_sum_smul (A := R) Γ a
      refine ⟨b • m, ?_⟩
      simp_rw [tensorAction_smul_tmul, ← TensorProduct.sum_tmul, ← hb]
      simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hsum : ∑ g : Γ, g • x = (Fintype.card Γ : R) • x := by
    rw [Finset.sum_congr rfl fun g _ ↦ hx g, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul R]
  have : x = (↑hΓ.unit⁻¹ : R) • ∑ g : Γ, g • x := by
    rw [hsum, smul_smul, IsUnit.val_inv_mul, one_smul]
  obtain ⟨m, hm⟩ := N.smul_mem (↑hΓ.unit⁻¹ : R) (key x)
  exact ⟨m, hm.trans this.symm⟩

variable (Γ) in
/-- The action of `Γ` on the integral closure of `R'` in `R' ⊗[R] M`. -/
@[instance_reducible]
noncomputable def integralClosureAction :
    MulSemiringAction Γ (integralClosure R' (R' ⊗[R] M)) :=
  letI := tensorAction (R := R) (R' := R') (M := M) Γ
  have hmem (g : Γ) (x : integralClosure R' (R' ⊗[R] M)) :
      g • (x : R' ⊗[R] M) ∈ integralClosure R' (R' ⊗[R] M) :=
    IsIntegral.map_of_comp_eq (MulSemiringAction.toRingHom Γ R' g)
      (MulSemiringAction.toRingHom Γ (R' ⊗[R] M) g)
      (RingHom.ext fun a ↦ (tensorAction_smul_algebraMap g a).symm) x.2
  { smul g x := ⟨g • (x : R' ⊗[R] M), hmem g x⟩
    one_smul x := Subtype.ext (one_smul Γ (x : R' ⊗[R] M))
    mul_smul g h x := Subtype.ext (mul_smul g h (x : R' ⊗[R] M))
    smul_zero g := Subtype.ext (smul_zero (A := R' ⊗[R] M) g)
    smul_add g x y := Subtype.ext (smul_add (A := R' ⊗[R] M) g x y)
    smul_one g := Subtype.ext (smul_one g : g • (1 : R' ⊗[R] M) = 1)
    smul_mul g x y := Subtype.ext
      (smul_mul' g (x : R' ⊗[R] M) (y : R' ⊗[R] M) :
        g • ((x : R' ⊗[R] M) * y) = g • (x : R' ⊗[R] M) * g • (y : R' ⊗[R] M)) }

lemma coe_integralClosureAction_smul (g : Γ) (x : integralClosure R' (R' ⊗[R] M)) :
    letI := integralClosureAction (R := R) (R' := R') (M := M) Γ
    letI := tensorAction (R := R) (R' := R') (M := M) Γ
    ((g • x : integralClosure R' (R' ⊗[R] M)) : R' ⊗[R] M) = g • (x : R' ⊗[R] M) :=
  rfl

/-- **Invariants of the integral closure of a base change.** If `R'^Γ = R`, `|Γ|` is invertible
and `M → R' ⊗[R] M` is injective, the `Γ`-invariant elements of the integral closure of `R'` in
`R' ⊗[R] M` are the `1 ⊗ t` with `t` integral over `R`. -/
theorem exists_eq_includeRight_of_forall_smul_eq_integralClosure [Finite Γ]
    (hΓ : IsUnit (Fintype.card Γ : R))
    (hinj : Function.Injective (Algebra.TensorProduct.includeRight : M →ₐ[R] R' ⊗[R] M))
    (x : integralClosure R' (R' ⊗[R] M))
    (hx : letI := integralClosureAction (R := R) (R' := R') (M := M) Γ; ∀ g : Γ, g • x = x) :
    ∃ t : integralClosure R M,
      Algebra.TensorProduct.includeRight (t : M) = (x : R' ⊗[R] M) := by
  letI := integralClosureAction (R := R) (R' := R') (M := M) Γ
  letI := tensorAction (R := R) (R' := R') (M := M) Γ
  obtain ⟨m, hm⟩ := mem_range_includeRight_of_forall_smul_eq hΓ (x : R' ⊗[R] M)
    fun g ↦ congr(Subtype.val $(hx g))
  have : Algebra.IsIntegral R R' := Algebra.IsInvariant.isIntegral R R' Γ
  have h1 : IsIntegral R (x : R' ⊗[R] M) := by
    exact isIntegral_trans (R := R) (A := R') _ x.2
  have h2 : IsIntegral R m := by
    rw [← isIntegral_algHom_iff _ hinj, hm]
    exact h1
  exact ⟨⟨m, h2⟩, hm⟩

end Algebra.IsInvariant
