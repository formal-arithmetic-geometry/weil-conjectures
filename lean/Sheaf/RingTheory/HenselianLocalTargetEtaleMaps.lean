/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.Basic
import WeilConjectures.RingTheory.HenselianEtaleRetraction
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Étale maps into a henselian local target

Source: Stacks Project, Algebra, Tags 04GG and 04GK.
-/

@[expose] public section

universe u v

open TensorProduct

namespace Algebra

/-- The pointed retraction criterion of Stacks 04GG (8), expressed as a residue-point lift. -/
private theorem existsUnique_etale_lift_residue
    (T C : Type v) [CommRing T] [CommRing C] [HenselianLocalRing T]
    [Algebra T C] [Etale T C] (χ : C →ₐ[T] IsLocalRing.ResidueField T) :
    ∃! σ : C →ₐ[T] T, ∀ c, IsLocalRing.residue T (σ c) = χ c := by
  let q := RingHom.ker χ.toRingHom
  have hχ : Function.Surjective χ := by
    intro x
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective (R := T) x
    exact ⟨algebraMap T C t, χ.commutes t⟩
  have : q.IsMaximal := RingHom.ker_isMaximal_of_surjective χ.toRingHom hχ
  have hq : q.comap (algebraMap T C) = IsLocalRing.maximalIdeal T := by
    ext t
    change χ (algebraMap T C t) = 0 ↔ t ∈ IsLocalRing.maximalIdeal T
    rw [χ.commutes, IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff]
  have hres : Function.Bijective
      (Ideal.ResidueField.map (IsLocalRing.maximalIdeal T) q (algebraMap T C) hq.symm) := by
    refine ⟨RingHom.injective _, ?_⟩
    intro x
    obtain ⟨c, rfl⟩ := q.algebraMap_residueField_surjective x
    obtain ⟨t, ht⟩ := IsLocalRing.residue_surjective (R := T) (χ c)
    refine ⟨algebraMap T (IsLocalRing.maximalIdeal T).ResidueField t, ?_⟩
    rw [Ideal.ResidueField.map_algebraMap]
    apply sub_eq_zero.mp
    rw [← map_sub, Ideal.algebraMap_residueField_eq_zero]
    change χ (algebraMap T C t - c) = 0
    simp only [map_sub, χ.commutes, IsLocalRing.ResidueField.algebraMap_eq, ht, sub_self]
  have : AlgebraicGeometry.Etale
      (AlgebraicGeometry.Scheme.Spec.map (CommRingCat.ofHom (algebraMap T C)).op) :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have h := existsUnique_algHom_of_henselianLocalRing_etale (algebraMap T C) q hq hres
  rw [toAlgebra_algebraMap] at h
  obtain ⟨σ, hσ, hu⟩ := h
  have hσred (c : C) : IsLocalRing.residue T (σ c) = χ c := by
    obtain ⟨t, ht⟩ := IsLocalRing.residue_surjective (R := T) (χ c)
    have hc : c - algebraMap T C t ∈ q := by
      change χ (c - algebraMap T C t) = 0
      simp only [map_sub, χ.commutes, IsLocalRing.ResidueField.algebraMap_eq, ht, sub_self]
    rw [← hσ] at hc
    have hh : IsLocalRing.residue T (σ (c - algebraMap T C t)) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hc
    simpa only [map_sub, σ.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_eq_zero, ht] using hh
  refine ⟨σ, hσred, ?_⟩
  intro τ hτ
  apply hu τ
  ext c
  change τ c ∈ IsLocalRing.maximalIdeal T ↔ χ c = 0
  rw [← IsLocalRing.residue_eq_zero_iff, hτ]

/-- Reduction of maps into a finite henselian local unramified algebra is bijective.
Source: Stacks Project, Algebra, Tag 04GG (8), applied after base change to the target;
Tag 04GK, full-faithfulness argument, local-target case.
(blueprint: lem-weil-pbc-henselian-local-target-etale-maps).

Proof: Since T is finite over the local ring R, its structure map is local. Formal
unramifiedness and finite type imply m_R T = m_T (Stacks 00UW). Hence κ_R ⊗_R T is
canonically the residue field κ_T. For a reduced map, compose S → κ_R ⊗_R S with
that map and identify the target with κ_T. Tensor adjunction turns the resulting
R-algebra map S → κ_T into a T-algebra map T ⊗_R S → κ_T. The algebra T ⊗_R S is
étale over the henselian local ring T. The unique pointed retraction of 04GG (8)
lifts this point to T. Tensor adjunction then gives the desired map S → T.
Two lifts yield retractions with the same inverse image of m_T, and so coincide by
the uniqueness in 04GG (8). Tensor adjunction identifies their reductions with the
original map, proving both surjectivity and injectivity. No finiteness of S is
needed. T is nonzero by its local-ring instance; S may be zero, in which case both
map sets are empty. -/
theorem bijective_residueField_tensor_map_of_henselian_target
    (R : Type u) [CommRing R] [IsLocalRing R]
    (S T : Type (max u v)) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Etale R S] [FormallyUnramified R T] [Module.Finite R T]
    [HenselianLocalRing T] :
    Function.Bijective
      (fun f : S →ₐ[R] T ↦
        (Algebra.TensorProduct.map
          (AlgHom.id (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R)) f :
          (IsLocalRing.ResidueField R ⊗[R] S) →ₐ[IsLocalRing.ResidueField R]
            (IsLocalRing.ResidueField R ⊗[R] T))) := by
  classical
  have : IsLocalHom (algebraMap R T) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap R T)).out 4 0).mp
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (IsLocalRing.maximalIdeal T))
  let k := IsLocalRing.ResidueField R
  let l := IsLocalRing.ResidueField T
  have hm : (IsLocalRing.maximalIdeal R).map (algebraMap R T) =
      IsLocalRing.maximalIdeal T := FormallyUnramified.map_maximalIdeal
  let q := Algebra.TensorProduct.quotIdealMapEquivQuotTensor T
    (IsLocalRing.maximalIdeal R)
  let eR : (k ⊗[R] T) ≃ₐ[R] l :=
    (q.symm.restrictScalars R).trans (Ideal.quotientEquivAlgOfEq R hm)
  let e : (k ⊗[R] T) ≃ₐ[k] l :=
    AlgEquiv.extendScalarsOfSurjective (IsLocalRing.residue_surjective (R := R)) eR
  have he (t : T) : e (1 ⊗ₜ[R] t) = IsLocalRing.residue T t := by
    change (Ideal.quotientEquivAlgOfEq R hm) (q.symm (1 ⊗ₜ[R] t)) = _
    have ht : q (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal R).map (algebraMap R T)) t) = 1 ⊗ₜ[R] t :=
      Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk T
        (IsLocalRing.maximalIdeal R) t
    rw [← ht, q.symm_apply_apply]
    rfl
  let adj : (S →ₐ[R] T) ≃ ((T ⊗[R] S) →ₐ[T] T) :=
    Algebra.TensorProduct.liftEquivRight (R := R) (S := T) (B := S) T
  let adj₀ : (S →ₐ[R] l) ≃ ((T ⊗[R] S) →ₐ[T] l) :=
    Algebra.TensorProduct.liftEquivRight (R := R) (S := T) (B := S) l
  have hred (f : S →ₐ[R] T) (s : S) :
      e (Algebra.TensorProduct.map (AlgHom.id k k) f (1 ⊗ₜ[R] s)) =
        IsLocalRing.residue T (f s) := by
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, he]
  change Function.Bijective (fun f : S →ₐ[R] T ↦
    (Algebra.TensorProduct.map (AlgHom.id k k) f : (k ⊗[R] S) →ₐ[k] (k ⊗[R] T)))
  constructor
  · intro f g hfg
    let χ : (T ⊗[R] S) →ₐ[T] l :=
      adj₀ ((IsScalarTower.toAlgHom R T l).comp f)
    obtain ⟨σ, _, hu⟩ := existsUnique_etale_lift_residue T (T ⊗[R] S) χ
    have hf : ∀ c, IsLocalRing.residue T (adj f c) = χ c := by
      intro c
      induction c with
      | zero => simp [χ]
      | tmul t s => simp [χ, adj, adj₀, Algebra.TensorProduct.liftEquivRight,
          l, IsLocalRing.ResidueField.algebraMap_eq]
      | add x y hx hy => simp_all only [map_add]
    have hg : ∀ c, IsLocalRing.residue T (adj g c) = χ c := by
      intro c
      induction c with
      | zero => simp [χ]
      | tmul t s =>
        have hh := congrArg (fun h ↦ e (h (1 ⊗ₜ[R] s))) hfg
        rw [hred, hred] at hh
        simp [χ, adj, adj₀, Algebra.TensorProduct.liftEquivRight,
          l, IsLocalRing.ResidueField.algebraMap_eq, hh]
      | add x y hx hy => simp_all only [map_add]
    exact adj.injective ((hu (adj f) hf).trans (hu (adj g) hg).symm)
  · intro f₀
    let χ₀ : S →ₐ[R] l :=
      (e.toAlgHom.restrictScalars R).comp
        ((f₀.restrictScalars R).comp Algebra.TensorProduct.includeRight)
    let χ := adj₀ χ₀
    obtain ⟨σ, hσ, _⟩ := existsUnique_etale_lift_residue T (T ⊗[R] S) χ
    let f := adj.symm σ
    refine ⟨f, ?_⟩
    apply AlgHom.ext
    intro x
    apply e.injective
    induction x with
    | zero => simp
    | tmul a s =>
      have hs := hσ (1 ⊗ₜ[R] s)
      have hf : IsLocalRing.residue T (f s) = e (f₀ (1 ⊗ₜ[R] s)) := by
        change IsLocalRing.residue T (σ (1 ⊗ₜ[R] s)) = _
        change IsLocalRing.residue T (σ (1 ⊗ₜ[R] s)) =
          Algebra.TensorProduct.lift (Algebra.ofId T l) χ₀
            (fun _ _ ↦ Commute.all _ _) (1 ⊗ₜ[R] s) at hs
        simp only [Algebra.TensorProduct.lift_tmul, map_one, one_mul] at hs
        exact hs
      rw [show a ⊗ₜ[R] s = a • (1 ⊗ₜ[R] s) by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      simp only [map_smul]
      rw [hred, hf]
    | add x y hx hy => simp_all only [map_add]

end Algebra
