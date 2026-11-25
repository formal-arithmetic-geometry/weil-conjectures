/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Finsupp.Defs
import WeilConjectures.AlgebraicGeometry.KoszulComplex

/-!
# Assembly of the last-generator exterior-power summands

For a free module with an extra last generator, every exterior power splits as
`⋀^(n+1) R^(r+1) ≃ ⋀^(n+1) R^r ⊕ ⋀^n R^r` via `(a, b) ↦ j(a) + e_last ∧ j(b)`.

## Implementation details

The inverse is `x ↦ (⋀(p)(x), ⋀(p)(contractLeft δ x))`, where `p` restricts to the prefix and
`δ` is the last coordinate. Contraction by `δ` kills the exterior algebra of the prefix, and
left induction proves `T(x) + e_last ∧ T(contractLeft δ x) = x` for `T = ⋀(j) ∘ ⋀(p)`.

## References

* [Stacks, Tags 0628, 0629]
-/

@[expose] public section

universe u

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R] (r : ℕ)

/-- The prefix inclusion sends the standard generator `i` to `i.castSucc`. -/
noncomputable def koszulPrefixInclusion : (Fin r →₀ R) →ₗ[R] Fin (r + 1) →₀ R :=
  Finsupp.lmapDomain R R Fin.castSucc

/-- Wedge on the left with the final standard generator, after prefix inclusion. -/
noncomputable def koszulLastWedge (n : ℕ) :
    ⋀[R]^n (Fin r →₀ R) →ₗ[R] ⋀[R]^(n + 1) (Fin (r + 1) →₀ R) :=
  (LinearMap.codRestrict (⋀[R]^(n + 1) (Fin (r + 1) →₀ R))
    { toFun := fun x ↦ ι R (Finsupp.single (Fin.last r) 1) * x.val
      map_add' := fun x y ↦ by simp [mul_add]
      map_smul' := fun c x ↦ by simp }
    (fun x ↦ by
      change _ ∈ (LinearMap.range (ι R)) ^ (n + 1)
      rw [Nat.add_comm n 1, pow_add, pow_one]
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self (ι R) _) x.property)).comp
    (exteriorPower.map n (koszulPrefixInclusion R r))

/-- The explicit assembly map `(a,b) ↦ inclusion(a) + e_last ∧ inclusion(b)`. -/
noncomputable def koszulLastAssembly (n : ℕ) :
    (⋀[R]^(n + 1) (Fin r →₀ R) × ⋀[R]^n (Fin r →₀ R)) →ₗ[R]
      ⋀[R]^(n + 1) (Fin (r + 1) →₀ R) :=
  LinearMap.coprod (exteriorPower.map (n + 1) (koszulPrefixInclusion R r))
    (koszulLastWedge R r n)

private noncomputable def prefixRetraction : (Fin (r + 1) →₀ R) →ₗ[R] Fin r →₀ R :=
  Finsupp.lcomapDomain Fin.castSucc (Fin.castSucc_injective r)

private theorem prefix_retraction_inclusion (v : Fin r →₀ R) :
    prefixRetraction R r (koszulPrefixInclusion R r v) = v :=
  Finsupp.leftInverse_lcomapDomain_mapDomain Fin.castSucc (Fin.castSucc_injective r) v

private theorem prefix_retraction_last :
    prefixRetraction R r (Finsupp.single (Fin.last r) 1) = 0 := by
  ext i
  simp [prefixRetraction]

private theorem prefix_decomposition (v : Fin (r + 1) →₀ R) :
    koszulPrefixInclusion R r (prefixRetraction R r v) +
      v (Fin.last r) • Finsupp.single (Fin.last r) 1 = v := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one, koszulPrefixInclusion, Finsupp.lmapDomain_apply]
    rw [Finsupp.mapDomain_of_notMem_range]
    · exact zero_add _
    · simp
  · simp [koszulPrefixInclusion, Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective r),
      prefixRetraction, Fin.castSucc_ne_last]

private theorem exterior_map_coe {E F : Type u} [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] (q : E →ₗ[R] F) (n : ℕ) (x : ⋀[R]^n E) :
    (exteriorPower.map n q x : ExteriorAlgebra R F) =
      ExteriorAlgebra.map q (x : ExteriorAlgebra R E) := by
  have h : (⋀[R]^n F).subtype.comp (exteriorPower.map n q) =
      (ExteriorAlgebra.map q).toLinearMap.comp (⋀[R]^n E).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, AlgHom.toLinearMap_apply]
    exact (ExteriorAlgebra.map_apply_ιMulti q v).symm
  exact LinearMap.congr_fun h x

private theorem last_form_inclusion (v : Fin r →₀ R) :
    Finsupp.linearCombination R (fun i : Fin (r + 1) ↦ if i = Fin.last r then (1 : R) else 0)
      (koszulPrefixInclusion R r v) = 0 := by
  rw [koszulPrefixInclusion, Finsupp.lmapDomain_apply, Finsupp.linearCombination_mapDomain]
  have h : ((fun i : Fin (r + 1) ↦ if i = Fin.last r then (1 : R) else 0) ∘
      Fin.castSucc) = fun _ : Fin r ↦ (0 : R) := by
    funext i
    simp [Fin.castSucc_ne_last]
  rw [h]
  simp [Finsupp.linearCombination_apply]

private theorem contract_last_prefix (x : ExteriorAlgebra R (Fin r →₀ R)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin (r + 1) →₀ R)))
      (Finsupp.linearCombination R
        (fun i ↦ if i = Fin.last r then (1 : R) else 0))
      (ExteriorAlgebra.map (koszulPrefixInclusion R r) x) = 0 := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | ι_mul x v hx =>
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      last_form_inclusion, zero_smul, hx, mul_zero, sub_zero]

private theorem exterior_projection_prefix (x : ExteriorAlgebra R (Fin r →₀ R)) :
    ExteriorAlgebra.map (prefixRetraction R r)
      (ExteriorAlgebra.map (koszulPrefixInclusion R r) x) = x := by
  induction x using CliffordAlgebra.induction with
  | algebraMap c => simp
  | ι v => simp [prefix_retraction_inclusion]
  | mul x y hx hy => simp only [map_mul, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem last_form_apply (v : Fin (r + 1) →₀ R) :
    Finsupp.linearCombination R (fun i ↦ if i = Fin.last r then (1 : R) else 0) v =
      v (Fin.last r) := by
  have h : Finsupp.linearCombination R
      (fun i : Fin (r + 1) ↦ if i = Fin.last r then (1 : R) else 0) =
      Finsupp.lapply (Fin.last r) := by
    ext i
    simp [Finsupp.lapply, Finsupp.single_apply]
  exact LinearMap.congr_fun h v

private theorem exterior_split (x : ExteriorAlgebra R (Fin (r + 1) →₀ R)) :
    ExteriorAlgebra.map (koszulPrefixInclusion R r)
      (ExteriorAlgebra.map (prefixRetraction R r) x) +
    ι R (Finsupp.single (Fin.last r) 1) *
      ExteriorAlgebra.map (koszulPrefixInclusion R r)
        (ExteriorAlgebra.map (prefixRetraction R r)
          (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin (r + 1) →₀ R)))
            (Finsupp.linearCombination R
              (fun i ↦ if i = Fin.last r then (1 : R) else 0)) x)) = x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => simp
  | add x y hx hy =>
    simp only [map_add, mul_add]
    rw [← add_add_add_comm, hx, hy]
  | ι_mul x v hx =>
    let L : ExteriorAlgebra R (Fin (r + 1) →₀ R) :=
      ι R (Finsupp.single (Fin.last r) 1)
    let W : ExteriorAlgebra R (Fin (r + 1) →₀ R) :=
      ι R (koszulPrefixInclusion R r (prefixRetraction R r v))
    let T := (ExteriorAlgebra.map (koszulPrefixInclusion R r)).comp
      (ExteriorAlgebra.map (prefixRetraction R r))
    let D := CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin (r + 1) →₀ R)))
      (Finsupp.linearCombination R (fun i ↦ if i = Fin.last r then (1 : R) else 0))
    have hW : W + v (Fin.last r) • L = ι R v := by
      dsimp [W, L]
      rw [← map_smul, ← map_add, prefix_decomposition]
    have hswap : W * L = -(L * W) :=
      eq_neg_of_add_eq_zero_left (ι_add_mul_swap _ _)
    have hL : L * L = 0 := ι_sq_zero _
    simp only [map_mul, ExteriorAlgebra.map_apply_ι]
    change W * T x + L * T (D (ι R v * x)) = ι R v * x
    have hDx : T (D (ι R v * x)) = v (Fin.last r) • T x - W * T (D x) := by
      simp only [D, CliffordAlgebra.contractLeft_ι_mul, last_form_apply,
        map_sub, map_smul, map_mul, T, AlgHom.comp_apply, ExteriorAlgebra.map_apply_ι]
      rfl
    rw [hDx, ← hW]
    change T x + L * T (D x) = x at hx
    conv_rhs => rw [← hx]
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
      ← mul_assoc, hswap, neg_mul, hL, smul_zero, add_zero, sub_eq_add_neg]
    abel_nf
    simp only [mul_smul_comm, ← mul_assoc]

/-- The last-generator assembly map `(a,b) ↦ inclusion(a) + e_last ∧ inclusion(b)` is
bijective in every degree. -/
theorem koszulLastAssembly_bijective (n : ℕ) :
    Function.Bijective (koszulLastAssembly R r n) := by
  let δ : Fin (r + 1) → R := fun i ↦ if i = Fin.last r then 1 else 0
  let inv (x : ⋀[R]^(n + 1) (Fin (r + 1) →₀ R)) :=
    (exteriorPower.map (n + 1) (prefixRetraction R r) x,
      exteriorPower.map n (prefixRetraction R r) (koszulBoundary R (r + 1) δ n x))
  have hleft : Function.LeftInverse inv (koszulLastAssembly R r n) := by
    rintro ⟨a, b⟩
    apply Prod.ext
    · apply Subtype.ext
      change (exteriorPower.map (n + 1) (prefixRetraction R r)
        (koszulLastAssembly R r n (a, b)) : ExteriorAlgebra R (Fin r →₀ R)) = a.val
      rw [exterior_map_coe]
      change ExteriorAlgebra.map (prefixRetraction R r)
        ((exteriorPower.map (n + 1) (koszulPrefixInclusion R r) a :
            ExteriorAlgebra R (Fin (r + 1) →₀ R)) +
          ι R (Finsupp.single (Fin.last r) 1) *
            (exteriorPower.map n (koszulPrefixInclusion R r) b :
              ExteriorAlgebra R (Fin (r + 1) →₀ R))) = _
      simp only [exterior_map_coe, map_add, map_mul, ExteriorAlgebra.map_apply_ι,
        prefix_retraction_last, map_zero, zero_mul, add_zero, exterior_projection_prefix]
    · apply Subtype.ext
      change (exteriorPower.map n (prefixRetraction R r)
        (koszulBoundary R (r + 1) δ n (koszulLastAssembly R r n (a, b))) :
          ExteriorAlgebra R (Fin r →₀ R)) = b.val
      rw [exterior_map_coe]
      change ExteriorAlgebra.map (prefixRetraction R r)
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin (r + 1) →₀ R)))
          (Finsupp.linearCombination R δ)
          ((exteriorPower.map (n + 1) (koszulPrefixInclusion R r) a :
              ExteriorAlgebra R (Fin (r + 1) →₀ R)) +
            ι R (Finsupp.single (Fin.last r) 1) *
              (exteriorPower.map n (koszulPrefixInclusion R r) b :
                ExteriorAlgebra R (Fin (r + 1) →₀ R)))) = _
      simp only [exterior_map_coe, map_add, δ, contract_last_prefix,
        CliffordAlgebra.contractLeft_ι_mul, Finsupp.linearCombination_single,
        ite_true, one_smul, mul_zero, sub_zero, zero_add, exterior_projection_prefix]
  have hright : Function.RightInverse inv (koszulLastAssembly R r n) := by
    intro x
    apply Subtype.ext
    change (exteriorPower.map (n + 1) (koszulPrefixInclusion R r)
      (exteriorPower.map (n + 1) (prefixRetraction R r) x) :
        ExteriorAlgebra R (Fin (r + 1) →₀ R)) +
      ι R (Finsupp.single (Fin.last r) 1) *
        (exteriorPower.map n (koszulPrefixInclusion R r)
          (exteriorPower.map n (prefixRetraction R r) (koszulBoundary R (r + 1) δ n x)) :
            ExteriorAlgebra R (Fin (r + 1) →₀ R)) = x.val
    simp only [exterior_map_coe]
    exact exterior_split R r x.val
  exact ⟨hleft.injective, hright.surjective⟩

end ExteriorAlgebra
