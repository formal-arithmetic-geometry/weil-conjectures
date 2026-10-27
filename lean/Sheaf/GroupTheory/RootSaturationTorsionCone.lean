/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Algebra.Order.Field.Rat

/-!
# Root saturation through the finite torsion quotient

Source: Illusie--Laszlo--Orgogozo, Exposé VIII, 3.1.17, printed p. 101, and the proof
of 3.2.9, printed p. 104. The torsion-quotient and denominator-clearing argument is
supplied in the DAG proof (blueprint: lem-trf-root-saturation-torsion-cone).
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped BigOperators TensorProduct

namespace AddCommGroup

private theorem common_denominator {r : ℕ} (q : Fin r → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∃ D : ℕ, 0 < D ∧ ∃ m : Fin r → ℕ, ∀ i, (D : ℚ) * q i = m i := by
  classical
  let D := ∏ i, (q i).den
  have hD : 0 < D := Finset.prod_pos fun i _ ↦ (q i).den_pos
  have hm : ∀ i, ∃ m : ℕ, (D : ℚ) * q i = m := by
    intro i
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun j : Fin r ↦ (q j).den)
      (Finset.mem_univ i)
    refine ⟨c * (q i).num.toNat, ?_⟩
    have hnum : ((q i).num.toNat : ℚ) = (q i).num := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hq i))
    change (D : ℚ) * q i = _
    rw [show D = (q i).den * c from hc, Nat.cast_mul, Nat.cast_mul,
      mul_comm ((q i).den : ℚ) (c : ℚ), mul_assoc, Rat.den_mul_eq_num, hnum]
  choose m hm using hm
  exact ⟨D, hD, m, hm⟩

private theorem cone_criterion
    {G V : Type u} [AddCommGroup G] [AddCommGroup V] [Module ℚ V]
    (f : G →+ V) (hker : ∀ g, f g = 0 ↔ g ∈ torsion G)
    (r : ℕ) (p : Fin r → G) (g : G) :
    (∃ n : ℕ, 0 < n ∧ ∃ m : Fin r → ℕ, n • g = ∑ i, m i • p i) ↔
      ∃ q : Fin r → ℚ, (∀ i, 0 ≤ q i) ∧ f g = ∑ i, q i • f (p i) := by
  constructor
  · rintro ⟨n, hn, m, heq⟩
    have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    refine ⟨fun i ↦ (m i : ℚ) / n,
      fun i ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
    have hf : (n : ℚ) • f g = ∑ i, (m i : ℚ) • f (p i) := by
      simpa only [map_nsmul, map_sum, Nat.cast_smul_eq_nsmul] using congrArg f heq
    calc
      f g = (n : ℚ)⁻¹ • ((n : ℚ) • f g) := (inv_smul_smul₀ hnq _).symm
      _ = ∑ i, ((m i : ℚ) / n) • f (p i) := by
        rw [hf, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul, div_eq_mul_inv, mul_comm]
  · rintro ⟨q, hq, heq⟩
    obtain ⟨D, hD, m, hm⟩ := common_denominator q hq
    have hf : f (D • g - ∑ i, m i • p i) = 0 := by
      rw [map_sub, map_nsmul, map_sum, sub_eq_zero]
      simp only [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, heq, Finset.smul_sum, smul_smul, hm]
    obtain ⟨k, hk, hkill⟩ := ((mem_torsion _).mp ((hker _).mp hf)).exists_nsmul_eq_zero
    have hh : (k * D) • g = ∑ i, (k * m i) • p i := by
      rw [smul_sub, sub_eq_zero, Finset.smul_sum] at hkill
      simpa only [smul_smul] using hkill
    exact ⟨k * D, Nat.mul_pos hk hD, fun i ↦ k * m i, hh⟩

private theorem tensor_one_injective
    {L : Type u} [AddCommGroup L] {s : ℕ} (b : Module.Basis (Fin s) ℤ L) :
    Function.Injective (fun l : L ↦ l ⊗ₜ[ℤ] (1 : ℚ)) := by
  intro x y h
  apply b.repr.injective
  ext i
  have hh := congrArg (fun z ↦ TensorProduct.lid ℤ ℚ
    (TensorProduct.map (b.coord i) (LinearMap.id : ℚ →ₗ[ℤ] ℚ) z)) h
  simpa using Rat.intCast_injective (by simpa using hh)

/-- For a finite group-generating list, torsion is finite, the torsion quotient has a finite
integral basis, its tensor embedding is injective, and positive-multiple membership in the
nonnegative integral span is equivalent to membership in the nonnegative rational cone.
The cone is written as sums of `π(p i) ⊗ q i`, namely `q i` times `π(p i) ⊗ 1`.

Source: ILO, Exposé VIII, 3.1.17, printed p. 101 (root saturation), and 3.2.9, proof,
printed p. 104 (finite toric saturation input); the following argument is agent supplied
(blueprint: lem-trf-root-saturation-torsion-cone).

Proof:
1. Apply `AddCommGroup.equiv_free_prod_directSum_zmod`
   (lem-sbc-finitely-generated-abelian-group-structure) to identify `G` with `ℤ^s × H`,
   where `H` is a finite sum of finite cyclic groups of positive orders `d j`.
   Their product `N`, with empty product `1`, kills `H`. An element `(a,h)` is torsion
   exactly when `a = 0`: cancel a positive multiplier in each integral coordinate for
   one implication, and use `N` for the other. Hence `T` is finite and `G/T ≃+ ℤ^s`.
   Transport the coordinate basis back to `G/T` (def-weil-pbc-free-module).
2. The basis coordinates identify `(G/T) ⊗[ℤ] ℚ` with `ℚ^s`: send `l ⊗ q` to the tuple
   of coordinates of `l` multiplied by `q`, with inverse the sum of basis tensors.
   Bilinearity and the tensor universal property (def-weil-pbc-module-tensor-product)
   show both composites are identities. The map `l ↦ l ⊗ 1` becomes the inclusion of
   integral tuples into rational tuples, so is injective, also for `s = 0`.
3. If `n • g = ∑ i, m i • p i` with `n > 0`, apply the quotient and tensor maps and
   divide by `n`. The coefficients `(m i : ℚ) / n` are nonnegative, proving membership
   in the rational cone by tensor bilinearity (def-weil-pbc-module-tensor-product).
4. Conversely write each nonnegative coefficient as `a i / b i` with natural `a i`
   and positive `b i`. Put `D = ∏ i, b i` and `m i = a i * ∏ j ≠ i, b j`, so
   `D * q i = m i`. Multiply the tensor equality by `D`. Bilinearity and the injectivity
   in step 2 show that `t = D • g - ∑ i, m i • p i` lies in `T`. Choose `k > 0` killing
   `t`; then `(k * D) • g = ∑ i, (k * m i) • p i`. For the empty list, `D = 1` and
   the sum is zero, and the same torsion-killing argument applies. -/
theorem root_saturation_torsion_cone
    {G : Type u} [AddCommGroup G] (r : ℕ) (p : Fin r → G)
    (hp : AddSubgroup.closure (Set.range p) = ⊤) :
    Finite (torsion G) ∧
      (∃ s : ℕ, Nonempty (Module.Basis (Fin s) ℤ (G ⧸ torsion G))) ∧
      Function.Injective (fun l : G ⧸ torsion G ↦ l ⊗ₜ[ℤ] (1 : ℚ)) ∧
      ∀ g : G,
        (∃ n : ℕ, 0 < n ∧ ∃ m : Fin r → ℕ, n • g = ∑ i, m i • p i) ↔
          ∃ q : Fin r → ℚ, (∀ i, 0 ≤ q i) ∧
            (QuotientAddGroup.mk' (torsion G) g) ⊗ₜ[ℤ] (1 : ℚ) =
              ∑ i, (QuotientAddGroup.mk' (torsion G) (p i)) ⊗ₜ[ℤ] q i := by
  classical
  let : AddGroup.FG G := AddGroup.fg_iff.mpr ⟨Set.range p, hp, Set.finite_range p⟩
  let : Module.Finite ℤ G := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have hfinite : Finite (torsion G) := by
    let T := (torsion G).toIntSubmodule
    have hT : Module.IsTorsion ℤ T := isAddTorsion_iff_isTorsion_int.mp fun t ↦ by
      apply (isOfFinAddOrder_iff_nsmul_eq_zero).mpr
      obtain ⟨n, hn, heq⟩ := ((mem_torsion _).mp t.property).exists_nsmul_eq_zero
      exact ⟨n, hn, Subtype.ext heq⟩
    exact Module.finite_of_fg_torsion T hT
  let L := G ⧸ torsion G
  let : Module.Finite ℤ L := Module.Finite.iff_addGroup_fg.mpr inferInstance
  obtain ⟨s, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := L)
  have hinj := tensor_one_injective b
  refine ⟨hfinite, ⟨s, ⟨b⟩⟩, hinj, ?_⟩
  let π := QuotientAddGroup.mk' (torsion G)
  let f : G →+ ℚ ⊗[ℤ] L := (TensorProduct.mk ℤ ℚ L (1 : ℚ)).toAddMonoidHom.comp π
  have hker : ∀ g, f g = 0 ↔ g ∈ torsion G := by
    intro g
    have ht : f g = 0 ↔ π g = 0 := by
      constructor
      · intro h
        apply hinj
        have hh := congrArg (TensorProduct.comm ℤ ℚ L) h
        simpa [f] using hh
      · intro h
        change (1 : ℚ) ⊗ₜ[ℤ] π g = 0
        rw [h, TensorProduct.tmul_zero]
    exact ht.trans (QuotientAddGroup.eq_zero_iff _)
  intro g
  rw [cone_criterion f hker r p g]
  constructor
  · rintro ⟨q, hq, heq⟩
    refine ⟨q, hq, ?_⟩
    have hh := congrArg (TensorProduct.comm ℤ ℚ L) heq
    simpa [L, f, π, TensorProduct.smul_tmul', smul_eq_mul] using hh
  · rintro ⟨q, hq, heq⟩
    refine ⟨q, hq, ?_⟩
    have hh := congrArg (TensorProduct.comm ℤ L ℚ) heq
    simpa [L, f, π, TensorProduct.smul_tmul', smul_eq_mul] using hh

end AddCommGroup
