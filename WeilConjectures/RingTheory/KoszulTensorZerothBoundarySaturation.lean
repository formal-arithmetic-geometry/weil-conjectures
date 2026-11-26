/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Saturation of the degree-zero Koszul boundaries

If `t` is a nonzerodivisor on `M/(f)M`, then the degree-zero boundaries of `K(f) ⊗ M` are
saturated with respect to `t`.

## Implementation details

The degree-one differential sends `e_i ⊗ m` to `f_i • m`, so its image is `(f) • ⊤` and the
zeroth term modulo boundaries is `M/(f)M`.

## References

* [Stacks, Tags 062F, 0623]
-/

@[expose] public section

universe u v

namespace ExteriorAlgebra

open scoped TensorProduct

private theorem koszulBoundary_zero_generator {R : Type u} [CommRing R]
    {r : ℕ} (f : Fin r → R) (v : Fin 1 → (Fin r →₀ R)) :
    koszulBoundary R r f 0 (_root_.exteriorPower.ιMulti R 1 v) =
      (_root_.exteriorPower.zeroEquiv R (Fin r →₀ R)).symm
        (Finsupp.linearCombination R f (v 0)) := by
  apply Subtype.ext
  simp [koszulBoundary, _root_.exteriorPower.zeroEquiv_symm_apply,
    ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι,
    Algebra.algebraMap_eq_smul_one]

private theorem koszulBoundary_zero_formula {R : Type u} [CommRing R]
    {r : ℕ} (f : Fin r → R) (x : ⋀[R]^1 (Fin r →₀ R)) :
    _root_.exteriorPower.zeroEquiv R (Fin r →₀ R) (koszulBoundary R r f 0 x) =
      Finsupp.linearCombination R f (_root_.exteriorPower.oneEquiv R (Fin r →₀ R) x) := by
  have he : (_root_.exteriorPower.zeroEquiv R (Fin r →₀ R)).toLinearMap.comp
      (koszulBoundary R r f 0) = (Finsupp.linearCombination R f).comp
        (_root_.exteriorPower.oneEquiv R (Fin r →₀ R)).toLinearMap := by
    apply _root_.exteriorPower.linearMap_ext
    ext v
    simp [koszulBoundary_zero_generator]
  exact LinearMap.congr_fun he x

private noncomputable def tensorZeroEquiv {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] (r : ℕ) :
    (⋀[R]^0 (Fin r →₀ R) ⊗[R] M) ≃ₗ[R] M :=
  (TensorProduct.congr (_root_.exteriorPower.zeroEquiv R (Fin r →₀ R))
    (LinearEquiv.refl R M)).trans (TensorProduct.lid R M)

private theorem tensorZeroEquiv_boundary_tmul {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] {r : ℕ} (f : Fin r → R)
    (x : ⋀[R]^1 (Fin r →₀ R)) (m : M) :
    tensorZeroEquiv M r ((koszulBoundary R r f 0).rTensor M (x ⊗ₜ[R] m)) =
      Finsupp.linearCombination R f
        (_root_.exteriorPower.oneEquiv R (Fin r →₀ R) x) • m := by
  simp [tensorZeroEquiv, koszulBoundary_zero_formula]

private theorem tensorZeroEquiv_boundary_range {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] {r : ℕ} (f : Fin r → R) :
    LinearMap.range ((tensorZeroEquiv M r).toLinearMap.comp
      ((koszulBoundary R r f 0).rTensor M)) =
      Ideal.ofList (List.ofFn f) • (⊤ : Submodule R M) := by
  have hI : Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
    apply congrArg Ideal.span
    ext x
    simp
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul x m =>
      change tensorZeroEquiv M r ((koszulBoundary R r f 0).rTensor M (x ⊗ₜ[R] m)) ∈ _
      rw [tensorZeroEquiv_boundary_tmul]
      apply Submodule.smul_mem_smul _ (Submodule.mem_top : m ∈ (⊤ : Submodule R M))
      rw [hI, ← Ideal.submodule_span_eq, ← Finsupp.range_linearCombination]
      exact LinearMap.mem_range_self _ _
    | add x y hx hy =>
      simpa only [map_add] using Submodule.add_mem _ hx hy
  · apply Submodule.smul_le.mpr
    intro t ht m _
    rw [hI, ← Ideal.submodule_span_eq, ← Finsupp.range_linearCombination] at ht
    obtain ⟨x, hx⟩ := ht
    refine ⟨(_root_.exteriorPower.oneEquiv R (Fin r →₀ R)).symm x ⊗ₜ[R] m, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [tensorZeroEquiv_boundary_tmul, LinearEquiv.apply_symm_apply, hx]

/-- If `t` is a nonzerodivisor on `M/(f)M` and `t • b` is a degree-zero boundary of
`K(f) ⊗ M`, then `b` is a degree-zero boundary. -/
theorem koszulTensor_zeroth_boundary_saturation {R : Type u} [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] {r : ℕ} (f : Fin r → R) (t : R)
    (h : IsSMulRegular (M ⧸ (Ideal.ofList (List.ofFn f) • ⊤ : Submodule R M)) t) :
    let A := koszulComplexTensor R r f M
    ∀ b : A.X 0, (∃ a : A.X 1, A.d 1 0 a = t • b) →
      ∃ c : A.X 1, A.d 1 0 c = b := by
  dsimp only
  intro b hb
  change ∃ c, (koszulBoundary R r f 0).rTensor M c = b
  let e := tensorZeroEquiv (R := R) M r
  let D := (koszulBoundary R r f 0).rTensor M
  let N : Submodule R M := Ideal.ofList (List.ofFn f) • ⊤
  have heD : LinearMap.range (e.toLinearMap.comp D) = N :=
    tensorZeroEquiv_boundary_range M f
  have ht : t • e b ∈ N := by
    obtain ⟨a, ha⟩ := hb
    have ha' : D a = t • b := by
      change D a = t • b at ha
      exact ha
    rw [← heD]
    refine ⟨a, ?_⟩
    change e (D a) = t • e b
    rw [ha', map_smul]
  have hz : N.mkQ (e b) = 0 := by
    apply h.right_eq_zero_of_smul
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero N).mpr ht
  have hm : e b ∈ LinearMap.range (e.toLinearMap.comp D) := by
    rw [heD]
    exact (Submodule.Quotient.mk_eq_zero N).mp hz
  obtain ⟨c, hc⟩ := hm
  exact ⟨c, e.injective hc⟩

end ExteriorAlgebra
