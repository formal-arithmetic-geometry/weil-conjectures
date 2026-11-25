/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.RingTheory.ProperBaseChange.GeometricallyNormalPerfectClosureCriterion

/-!
# Separable field extensions are geometrically normal

A separable field extension `K/k` is geometrically normal: `E ⊗[k] K` is normal for every field
extension `E/k`.

## Implementation details

Choose a perfect purely inseparable overfield `P/k` and put `R = K ⊗[k] P`. Each element of `R`
lies in the image of `F ⊗[k] P` for a finitely generated, hence separably generated,
intermediate field `F`; these are reduced, so `R` is reduced. Some `q^n`-th power of each element
lies in the image of `K`, and a coordinate functional on a `k`-basis of `P` shows `R ≠ 0`; hence
`R` is a field. The perfect-closure criterion for geometric normality then gives normality of
`E ⊗[k] K` for arbitrary `E/k`.

## References

* [Stacks, Tag 0C30]
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

private theorem reduced_tensor_separable
    (k : Type u) (K : Type v) (P : Type w)
    [Field k] [Field K] [Field P] [Algebra k K] [Algebra k P]
    (hK : IsSeparableExtension k K) : IsReduced (P ⊗[k] K) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB ↦ ?_
  obtain ⟨s, hs⟩ := hB
  let F := IntermediateField.adjoin k (s : Set K)
  have hBF : B ≤ F.toSubalgebra := by
    rw [← hs]
    exact Algebra.adjoin_le (IntermediateField.subset_adjoin k _)
  let i : B →ₐ[k] F := Subalgebra.inclusion hBF
  have : IsReduced (F ⊗[k] P) :=
    isReduced_tensorProduct_of_isSeparablyGenerated k F P
      (hK F (IntermediateField.fg_adjoin_finset s))
  have : IsReduced (P ⊗[k] F) :=
    isReduced_of_injective (TensorProduct.comm k P F) (AlgEquiv.injective _)
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : F ↦ (z : K)) h)
  exact isReduced_of_injective (TensorProduct.map (AlgHom.id k P) i)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hi)

private theorem field_tensor_purely_inseparable
    (k : Type u) (K : Type v) (P : Type w)
    [Field k] [Field K] [Field P] [Algebra k K] [Algebra k P]
    [IsPurelyInseparable k P] [IsReduced (K ⊗[k] P)] : IsField (K ⊗[k] P) := by
  let : Nontrivial (K ⊗[k] P) :=
    (TensorProduct.includeLeft_injective (R := k) (S := k) (A := K) (B := P)
      (algebraMap k P).injective).nontrivial
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro z hz
  obtain ⟨n, hn, c, hc⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct z
  have hc0 : c ≠ 0 := by
    intro h
    apply hz
    exact IsReduced.eq_zero z ⟨n, by simpa [h] using hc.symm⟩
  have hu : IsUnit (z ^ n) := hc ▸ (isUnit_iff_ne_zero.mpr hc0).map (algebraMap K _)
  exact ((isUnit_pow_iff hn.ne').mp hu).exists_right_inv

private theorem normal_of_equiv {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (e : R ≃+* S)
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  intro q hq
  let p := q.comap e.toRingHom
  let : p.IsPrime := Ideal.comap_isPrime e.toRingHom q
  obtain ⟨hd, hi⟩ := hR p
  let : IsDomain (Localization.AtPrime p) := hd
  let : IsIntegrallyClosed (Localization.AtPrime p) := hi
  let e' := Localization.localRingEquiv p q e rfl
  exact ⟨e'.symm.injective.isDomain e'.symm, IsIntegrallyClosed.of_equiv e'⟩

private theorem normal_of_field (R : Type u) [Field R] :
    ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  intro p hp
  let e := RingEquiv.ofBijective (algebraMap R (Localization.AtPrime p))
    (Field.localization_map_bijective (M := p.primeCompl) (by simp))
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e⟩

/-- A separable field extension remains normal after tensoring with any field extension.
Here separability means that every finitely generated intermediate field is separably generated;
neither extension is required to be algebraic or finitely generated. -/
theorem normal_tensorProduct_of_isSeparableExtension
    (k : Type u) (K : Type v) (E : Type w)
    [Field k] [Field K] [Field E] [Algebra k K] [Algebra k E]
    (hK : IsSeparableExtension k K) :
    ∀ (p : Ideal (K ⊗[k] E)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let P := perfectClosure k (AlgebraicClosure k)
  have hpower : ∀ x : P, ∃ n : ℕ, ∃ a : k,
      algebraMap k P a = x ^ (ringExpChar k ^ n) :=
    fun x ↦ IsPurelyInseparable.pow_mem k (ringExpChar k) x
  have : IsReduced (P ⊗[k] K) := reduced_tensor_separable k K P hK
  have : IsReduced (K ⊗[k] P) :=
    isReduced_of_injective (TensorProduct.comm k K P) (AlgEquiv.injective _)
  let : Field (K ⊗[k] P) := (field_tensor_purely_inseparable k K P).toField
  have hP := normal_of_equiv (TensorProduct.comm k K P).toRingEquiv
    (normal_of_field (K ⊗[k] P))
  have h := (normal_tensor_perfectClosure_iff.{u, v, u, w} k K P hpower).mp hP
    (ULift.{max u v} E)
  let e : (ULift.{max u v} E ⊗[k] K) ≃ₐ[k] (K ⊗[k] E) :=
    (TensorProduct.congr (ULift.algEquiv : ULift.{max u v} E ≃ₐ[k] E)
      (AlgEquiv.refl : K ≃ₐ[k] K)).trans (TensorProduct.comm k E K)
  exact normal_of_equiv e.toRingEquiv h

end Algebra
