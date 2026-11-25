/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import WeilConjectures.FieldTheory.SeparableExtension
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Field.ULift

/-!
# Geometrically reduced field extensions are separable in positive characteristic

We show that a geometrically reduced field extension in characteristic `p` is separable
(`Algebra.isSeparableExtension_of_forall_isReduced_tensorProduct`).

## Implementation details

Applying the hypothesis to `L = k^{1/p}` inside an algebraic closure, for `bᵢ ∈ K` and `cᵢ ∈ k` the
element `x = ∑ bᵢ ⊗ cᵢ^{1/p}` satisfies `x ^ p = (∑ cᵢ bᵢ ^ p) ⊗ 1`. Reducedness shows that
`k`-linearly independent elements have `k`-linearly independent `p`-th powers. This passes to
finitely generated intermediate fields, which are then separably generated.

## References

* [Stacks Project, Tag 030W](https://stacks.math.columbia.edu/tag/030W), (4) ⇒ (1)
* [Stacks Project, Tag 030S](https://stacks.math.columbia.edu/tag/030S)
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- In prime characteristic `p`, if `K ⊗[k] L` is reduced for every field extension `L/k`, then
`K/k` is separable: every finitely generated intermediate field is separably generated. -/
theorem isSeparableExtension_of_forall_isReduced_tensorProduct
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hred : ∀ (L : Type (max u v)) [Field L] [Algebra k L],
      IsReduced (K ⊗[k] L)) :
    Algebra.IsSeparableExtension k K := by
  classical
  -- Frobenius independence, using roots in a universe-lifted algebraic closure.
  have hpow : ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) →
        LinearIndepOn k (· ^ p) (s : Set K) := by
    let L := ULift.{v} (AlgebraicClosure k)
    let : IsReduced (K ⊗[k] L) := hred L
    let : IsReduced (L ⊗[k] K) :=
      isReduced_of_injective (Algebra.TensorProduct.comm k L K)
        (Algebra.TensorProduct.comm k L K).injective
    let : Nontrivial (L ⊗[k] K) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
        k L K (algebraMap k K).injective
    let : CharP (L ⊗[k] K) p :=
      charP_of_injective_algebraMap (algebraMap k (L ⊗[k] K)).injective p
    intro s hs
    rw [linearIndepOn_finset_iff]
    intro c hc i hi
    have hroot (x : K) : ∃ r : L, r ^ p = algebraMap k L (c x) := by
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq
        (algebraMap k (AlgebraicClosure k) (c x)) (Fact.out : p.Prime).pos
      exact ⟨ULift.up r, congrArg ULift.up hr⟩
    choose r hr using hroot
    have hz : (∑ x ∈ s, r x ⊗ₜ[k] x : L ⊗[k] K) ^ p = 0 := by
      rw [sum_pow_char]
      have heq : (∑ x ∈ s, (r x ⊗ₜ[k] x : L ⊗[k] K) ^ p) =
          ∑ x ∈ s, (r x ^ p) ⊗ₜ[k] (x ^ p) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact Algebra.TensorProduct.tmul_pow (R := k) (r x) x p
      rw [heq]
      simp_rw [hr]
      have hterm (x : K) :
          (algebraMap k L (c x)) ⊗ₜ[k] (x ^ p) = (1 : L) ⊗ₜ[k] (c x • x ^ p) := by
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      simp_rw [hterm]
      rw [← TensorProduct.tmul_sum, hc, TensorProduct.tmul_zero]
    have hz' : (∑ x ∈ s, r x ⊗ₜ[k] x : L ⊗[k] K) = 0 :=
      IsReduced.eq_zero _ ⟨p, hz⟩
    have hli : LinearIndependent L (fun x : s ↦ (1 : L) ⊗ₜ[k] (x : K)) :=
      Module.Flat.linearIndependent_one_tmul hs
    rw [← s.sum_attach (fun x ↦ r x ⊗ₜ[k] x)] at hz'
    have hsum : (∑ x : s, r x • ((1 : L) ⊗ₜ[k] (x : K))) = 0 := by
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Finset.attach_eq_univ] using hz'
    have hri : r i = 0 := (Fintype.linearIndependent_iff.mp hli) (fun x : s ↦ r x) hsum ⟨i, hi⟩
    apply (algebraMap k L).injective
    simpa [hri, zero_pow (Fact.out : p.Prime).ne_zero] using (hr i).symm
  -- Transfer the criterion to each finitely generated intermediate field.
  intro F hF
  let : Algebra.EssFiniteType k F := IntermediateField.essFiniteType_iff.mpr hF
  have hFpow : ∀ s : Finset F,
      LinearIndepOn k _root_.id (s : Set F) →
        LinearIndepOn k (· ^ p) (s : Set F) := by
    intro s hs
    have hi : Function.Injective F.val := Subtype.val_injective
    have hs' : LinearIndepOn k (fun x : F ↦ (x : K)) (s : Set F) :=
      hs.map_injOn F.val.toLinearMap hi.injOn
    have h := hpow (s.image fun x : F ↦ (x : K)) (by
      simpa only [Finset.coe_image] using hs'.id_image)
    rw [Finset.coe_image] at h
    have h' := h.comp_of_image hi.injOn
    apply (F.val.toLinearMap.linearIndepOn_iff_of_injOn hi.injOn).mp
    change LinearIndepOn k (fun x : F ↦ ((x ^ p : F) : K)) (s : Set F)
    simpa only [Function.comp_def, IntermediateField.coe_pow] using h'
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      p (Fact.out : p.Prime) hFpow
  exact ⟨(s : Set F), hs, hsep⟩

end Algebra
