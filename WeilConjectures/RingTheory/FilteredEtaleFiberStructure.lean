/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Unramified.Field
import WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise

/-! # Reduced zero-dimensional fibres of filtered etale colimits

The fibres of a filtered colimit of etale algebras are reduced and zero-dimensional.

## Implementation details

Tensor products commute with filtered colimits, so every fibre element lifts to a stage and a
zero element vanishes at a later stage (Tags 00DD, 00D6, 00D7). Stage fibres are etale over a
field, hence finite products of finite separable field extensions (Tag 00U3), so reduced with
all primes maximal; both properties pass to the colimit. The zero ring is allowed, and no
Noetherian hypothesis is needed.

## References

* [Stacks, Tag 0AH1], first paragraph of the proof
* [Stacks, Tag 00DD], [Stacks, Tag 00D6], [Stacks, Tag 00D7], [Stacks, Tag 00U3]
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace CommAlgCat

/-- Fibres of filtered colimits of etale algebras are reduced and zero-dimensional. -/
theorem filteredEtale_fiber_structure
    (A : Type u) [CommRing A]
    {I : Type v} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CommAlgCat.{v} A) [HasColimit D]
    (hD : ∀ i : I, Algebra.Etale A (D.obj i))
    (p : PrimeSpectrum A) :
    IsReduced (p.asIdeal.Fiber ↥(colimit D)) ∧
      Ring.KrullDimLE 0 (p.asIdeal.Fiber ↥(colimit D)) := by
  let κ := p.asIdeal.ResidueField
  let B := ↥(colimit D)
  let C := p.asIdeal.Fiber B
  let Ci (i : I) := p.asIdeal.Fiber ↥(D.obj i)
  let γ (i : I) : Ci i →ₐ[κ] C :=
    Algebra.TensorProduct.lTensor κ (colimit.ι D i).hom
  let τ {i j : I} (u : i ⟶ j) : Ci i →ₐ[κ] Ci j :=
    Algebra.TensorProduct.lTensor κ (D.map u).hom
  have hstage (i : I) : IsReduced (Ci i) ∧ IsArtinianRing (Ci i) := by
    let : Algebra.Etale A ↥(D.obj i) := hD i
    let : Algebra.Etale κ (Ci i) := inferInstance
    have := Algebra.FormallyUnramified.finite_of_free κ (Ci i)
    exact ⟨Algebra.FormallyUnramified.isReduced_of_field κ (Ci i),
      IsArtinianRing.of_finite κ (Ci i)⟩
  obtain ⟨hlift, hzero⟩ := filteredColimit_tensorProduct_elementwise A D κ
  have hlift' (x : C) : ∃ i : I, ∃ y : Ci i, γ i y = x := by
    obtain ⟨i, y, hy⟩ := hlift (Algebra.TensorProduct.comm A κ B x)
    refine ⟨i, Algebra.TensorProduct.comm A ↥(D.obj i) κ y, ?_⟩
    change LinearMap.lTensor κ (colimit.ι D i).hom.toLinearMap
      (_root_.TensorProduct.comm A ↥(D.obj i) κ y) = x
    rw [LinearMap.lTensor_comm, hy]
    exact (Algebra.TensorProduct.comm A κ B).symm_apply_apply x
  have hzero' (i : I) (y : Ci i) (hy : γ i y = 0) :
      ∃ j : I, ∃ u : i ⟶ j, τ u y = 0 := by
    have hy' : LinearMap.rTensor κ (colimit.ι D i).hom.toLinearMap
        (_root_.TensorProduct.comm A κ ↥(D.obj i) y) = 0 := by
      rw [LinearMap.rTensor_comm]
      change Algebra.TensorProduct.comm A κ B (γ i y) = 0
      rw [hy, map_zero]
    obtain ⟨j, u, hu⟩ := hzero i _ hy'
    refine ⟨j, u, ?_⟩
    apply (Algebra.TensorProduct.comm A κ ↥(D.obj j)).injective
    rw [map_zero]
    exact (LinearMap.rTensor_comm (D.map u).hom.toLinearMap y).symm.trans hu
  constructor
  · refine ⟨fun x hx ↦ ?_⟩
    obtain ⟨i, y, rfl⟩ := hlift' x
    obtain ⟨n, hn⟩ := hx
    obtain ⟨j, u, hu⟩ := hzero' i (y ^ n) (by simpa using hn)
    let : IsReduced (Ci j) := (hstage j).1
    have hτ : τ u y = 0 := eq_zero_of_pow_eq_zero (by simpa using hu)
    have hcompat : (γ j).comp (τ u) = γ i := by
      have hw : (colimit.ι D j).hom.comp (D.map u).hom = (colimit.ι D i).hom :=
        congrArg CommAlgCat.Hom.hom (colimit.w D u)
      ext b
      change (1 : κ) ⊗ₜ[A] (colimit.ι D j).hom ((D.map u).hom b) =
        (1 : κ) ⊗ₜ[A] (colimit.ι D i).hom b
      exact congrArg (fun f : ↥(D.obj i) →ₐ[A] B ↦ (1 : κ) ⊗ₜ[A] f b) hw
    rw [← hcompat, AlgHom.comp_apply, hτ, map_zero]
  · apply Ring.krullDimLE_zero_iff.mpr
    intro Q hQ
    obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q hQ.ne_top
    have hEQ : Q = M := by
      apply le_antisymm hQM
      intro x hx
      obtain ⟨i, y, rfl⟩ := hlift' x
      let : IsArtinianRing (Ci i) := (hstage i).2
      let : (Q.comap (γ i).toRingHom).IsPrime := hQ.comap (γ i).toRingHom
      let : (M.comap (γ i).toRingHom).IsPrime := hM.isPrime.comap (γ i).toRingHom
      have hc : Q.comap (γ i).toRingHom = M.comap (γ i).toRingHom :=
        (IsArtinianRing.isMaximal_of_isPrime (Q.comap (γ i).toRingHom)).eq_of_le
          (inferInstance : (M.comap (γ i).toRingHom).IsPrime).ne_top (Ideal.comap_mono hQM)
      change y ∈ Q.comap (γ i).toRingHom
      rw [hc]
      exact hx
    exact hEQ.symm ▸ hM

end CommAlgCat
