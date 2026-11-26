/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic

import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Differential decomposition of a simple transcendental field extension

For a simple purely transcendental extension `F` of `F₀` over a field `k`, the module `Ω[F/k]`
splits as `F ⊗[F₀] Ω[F₀/k]` plus a free part spanned by the differential of the transcendental
generator.

## References

* [Stacks, Tag 00RS]
* [Stacks, Tag 00RX]
* [Stacks, Tag 00RT]
* [Stacks, Tag 00S2]
* [Stacks, Tag 07FI]
-/

@[expose] public section

set_option autoImplicit false
universe u v w

open scoped TensorProduct

namespace KaehlerDifferential

/-- The differentials of a simple rational extension split into base differentials
and the differential of the transcendental generator. -/
theorem exists_simple_transcendental_differential_decomposition
    (k : Type u) (F₀ : Type v) (F : Type w) [Field k] [Field F₀] [Field F]
    [Algebra k F₀] [Algebra k F] [Algebra F₀ F] [IsScalarTower k F₀ F]
    (m : ℕ) (y : Fin m → F) (hm : m = 1)
    (hy : ∀ j, Transcendental F₀ (y j))
    (hgen : IntermediateField.adjoin F₀ (Set.range y) = ⊤) :
    ∃ E : ((F ⊗[F₀] KaehlerDifferential k F₀) × (Fin m → F)) ≃ₗ[F]
        KaehlerDifferential k F,
      ∀ (x : F ⊗[F₀] KaehlerDifferential k F₀) (c : Fin m → F),
        E (x, c) = mapBaseChange k F₀ F x + ∑ j, c j • D k F (y j) := by
  classical
  subst m
  have hind : AlgebraicIndependent F₀ y :=
    algebraicIndependent_unique_type_iff.mpr (hy default)
  let P := MvPolynomial (Fin 1) F₀
  let A := Algebra.adjoin F₀ (Set.range y)
  let e : P ≃ₐ[F₀] A := hind.aevalEquiv
  let : Algebra P F := (MvPolynomial.aeval y).toRingHom.toAlgebra
  have : IsScalarTower F₀ P F := IsScalarTower.of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  let : Algebra A F := A.val.toRingHom.toAlgebra
  have : FaithfulSMul A F :=
    (faithfulSMul_iff_algebraMap_injective A F).mpr Subtype.val_injective
  have : IsFractionRing A F := IsFractionRing.of_field _ _ fun f ↦ by
    have hf : f ∈ IntermediateField.adjoin F₀ (Set.range y) := by rw [hgen]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := IntermediateField.mem_adjoin_iff_div.mp hf
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩
  have : IsFractionRing P F := IsFractionRing.of_ringEquiv_left e.toRingEquiv fun p ↦ by
    change MvPolynomial.aeval y p = (e p : F)
    exact (hind.algebraMap_aevalEquiv p).symm
  have : Algebra.FormallyEtale P F :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors P)
  let brel := ((mvPolynomialBasis F₀ (Fin 1)).baseChange F).map
    (tensorKaehlerEquivOfFormallyEtale F₀ P F)
  have hbrel (j : Fin 1) : brel j = D F₀ F (y j) := by
    rw [Module.Basis.map_apply, Module.Basis.baseChange_apply]
    change (tensorKaehlerEquivOfFormallyEtale F₀ P F)
      (1 ⊗ₜ[P] (mvPolynomialBasis F₀ (Fin 1)) j) = D F₀ F (y j)
    rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul,
      one_smul, mvPolynomialBasis_apply, map_D]
    congr 1
    exact MvPolynomial.aeval_X y j
  have : Algebra.FormallySmooth F₀ F :=
    Algebra.FormallySmooth.of_algebraicIndependent hind hgen
  let u := mapBaseChange k F₀ F
  let v := map k F₀ F F
  have hu : Function.Injective u := by
    apply (LinearMap.injective_iff_eq_zero_of_exact
      (Algebra.H1Cotangent.exact_δ_mapBaseChange k F₀ F)).mpr
    ext x
    simp only [Subsingleton.elim x 0, map_zero]
  let s : (Fin 1 → F) →ₗ[F] KaehlerDifferential k F :=
    { toFun := fun c ↦ ∑ j, c j • D k F (y j)
      map_add' := by intro b c; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro a b; simp [mul_smul] }
  let q := brel.equivFun
  have hvs (c : Fin 1 → F) : v (s c) = q.symm c := by
    simp [s, v, Module.Basis.equivFun_symm_apply, q, hbrel]
  have hvu (x : F ⊗[F₀] KaehlerDifferential k F₀) : v (u x) = 0 :=
    (exact_mapBaseChange_map k F₀ F (u x)).mpr ⟨x, rfl⟩
  let f : ((F ⊗[F₀] KaehlerDifferential k F₀) × (Fin 1 → F)) →ₗ[F]
      KaehlerDifferential k F :=
    u.comp (LinearMap.fst F _ _) + s.comp (LinearMap.snd F _ _)
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have hc : x.2 = y.2 := q.symm.injective (by
        simpa only [f, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.fst_apply, LinearMap.snd_apply, map_add, hvu, hvs, zero_add]
          using congrArg v h)
      exact Prod.ext (hu (by
        simpa only [f, LinearMap.add_apply, LinearMap.comp_apply,
          LinearMap.fst_apply, LinearMap.snd_apply, hc, add_left_inj] using h)) hc
    · intro ω
      let c := q (v ω)
      obtain ⟨x, hx⟩ := (exact_mapBaseChange_map k F₀ F (ω - s c)).mp (by
        rw [map_sub, hvs]; simp [c, v])
      exact ⟨(x, c), by
        change u x + s c = ω
        rw [hx, sub_add_cancel]⟩
  exact ⟨LinearEquiv.ofBijective f hf, fun x c ↦ rfl⟩

end KaehlerDifferential
