/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Top exterior power of a direct sum

## Main statements

* `exteriorPower.existsUnique_topDirectSum`: the canonical isomorphism characterized on wedges.
* `exteriorPower.topDirectSum_natural`: its compatibility with isomorphisms of the two modules.
-/

@[expose] public section

universe u v w v' w'

open scoped TensorProduct

namespace exteriorPower

/-- Multiply homogeneous elements after applying the two inclusions into the direct sum.
The product has degree `r + s` by the exterior-algebra grading. -/
private noncomputable def directSumMap
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (r s : ℕ) :
    ((⋀[R]^r M) ⊗[R] (⋀[R]^s N)) →ₗ[R] ⋀[R]^(r + s) (M × N) :=
  TensorProduct.lift
    { toFun := fun a ↦
        { toFun := fun b ↦
            ⟨((map r (LinearMap.inl R M N) a : ⋀[R]^r (M × N)) :
                ExteriorAlgebra R (M × N)) *
              ((map s (LinearMap.inr R M N) b : ⋀[R]^s (M × N)) :
                ExteriorAlgebra R (M × N)),
              SetLike.mul_mem_graded (map r (LinearMap.inl R M N) a).property
                (map s (LinearMap.inr R M N) b).property⟩
          map_add' := by intros; apply Subtype.ext; simp [mul_add]
          map_smul' := by intros; apply Subtype.ext; simp }
      map_add' := by
        intros
        apply LinearMap.ext
        intro b
        apply Subtype.ext
        simp [add_mul]
      map_smul' := by
        intros
        apply LinearMap.ext
        intro b
        apply Subtype.ext
        simp }

/-- Multiplication of the two homogeneous wedges concatenates their factors. -/
private theorem directSumMap_ιMulti
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (r s : ℕ) (m : Fin r → M) (n : Fin s → N) :
    directSumMap r s ((ιMulti R r m) ⊗ₜ[R] (ιMulti R s n)) =
      ιMulti R (r + s) (Fin.append (fun i ↦ (m i, 0)) (fun j ↦ (0, n j))) := by
  apply Subtype.ext
  change ((map r (LinearMap.inl R M N) (ιMulti R r m) :
      ⋀[R]^r (M × N)) : ExteriorAlgebra R (M × N)) *
    ((map s (LinearMap.inr R M N) (ιMulti R s n) :
      ⋀[R]^s (M × N)) : ExteriorAlgebra R (M × N)) = _
  simp only [map_apply_ιMulti, ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti]
  rfl

private noncomputable def topIndexEquiv (n : ℕ) :
    Set.powersetCard (Fin n) n ≃ Unit where
  toFun := fun _ ↦ ()
  invFun := fun _ ↦ ⟨Finset.univ, by simp⟩
  left_inv := by
    intro a
    apply Subtype.ext
    symm
    apply Finset.eq_univ_of_card
    simpa only [Fintype.card_fin] using Set.powersetCard.card_eq a
  right_inv := by intro a; cases a; rfl

private noncomputable def topBasis
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (n : ℕ) (b : Module.Basis (Fin n) R M) :
    Module.Basis Unit R (⋀[R]^n M) :=
  (b.exteriorPower n).reindex (topIndexEquiv n)

private theorem topBasis_apply
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    (n : ℕ) (b : Module.Basis (Fin n) R M) (i : Unit) :
    topBasis n b i = ιMulti R n b := by
  rw [topBasis, Module.Basis.reindex_apply, basis_apply]
  unfold ιMulti_family
  congr 1
  funext j
  exact congrArg b
    ((Set.powersetCard.ofFinEmbEquiv.symm ((topIndexEquiv n).symm i)).strictMono.apply_eq)

private theorem directSumMap_bijective
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (r s : ℕ)
    (bM : Module.Basis (Fin r) R M) (bN : Module.Basis (Fin s) R N) :
    Function.Bijective (directSumMap (R := R) (M := M) (N := N) r s) := by
  let b := (bM.prod bN).reindex finSumFinEquiv
  let a := (topBasis r bM).tensorProduct (topBasis s bN)
  let c := topBasis (r + s) b
  let eqv : Unit × Unit ≃ Unit :=
    { toFun := fun _ ↦ ()
      invFun := fun _ ↦ ((), ())
      left_inv := by rintro ⟨⟨⟩, ⟨⟩⟩; rfl
      right_inv := by rintro ⟨⟩; rfl }
  have h : directSumMap r s = (a.equiv c eqv).toLinearMap := by
    apply a.ext
    rintro ⟨i, j⟩
    rw [LinearEquiv.coe_toLinearMap, Module.Basis.equiv_apply]
    simp only [a, Module.Basis.tensorProduct_apply, topBasis_apply, directSumMap_ιMulti,
      c, topBasis_apply]
    congr 1
    funext j
    refine Fin.addCases ?_ ?_ j
    · intro k
      simp [b, Module.Basis.prod_apply]
    · intro k
      simp [b, Module.Basis.prod_apply]
  rw [h]
  exact (a.equiv c eqv).bijective

private theorem tensor_wedge_ext
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    {P : Type*} [AddCommGroup P] [Module R P]
    (r s : ℕ) {a b : ((⋀[R]^r M) ⊗[R] (⋀[R]^s N)) →ₗ[R] P}
    (h : ∀ m n, a ((ιMulti R r m) ⊗ₜ[R] (ιMulti R s n)) =
      b ((ιMulti R r m) ⊗ₜ[R] (ιMulti R s n))) : a = b := by
  apply TensorProduct.ext
  apply linearMap_ext
  apply AlternatingMap.ext
  intro m
  apply linearMap_ext
  apply AlternatingMap.ext
  intro n
  exact h m n

/-- For free modules `M` and `N` of ranks `r` and `s`, there is a unique isomorphism
`⋀^(r + s) (M × N) ≃ ⋀^r M ⊗ ⋀^s N` whose inverse sends `(m₁ ∧ ⋯ ∧ m_r) ⊗ (n₁ ∧ ⋯ ∧ n_s)` to
`(m₁, 0) ∧ ⋯ ∧ (m_r, 0) ∧ (0, n₁) ∧ ⋯ ∧ (0, n_s)`. -/
theorem existsUnique_topDirectSum
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (r s : ℕ) (_bM : Module.Basis (Fin r) R M) (_bN : Module.Basis (Fin s) R N) :
    ∃! e : (⋀[R]^(r + s) (M × N)) ≃ₗ[R] ((⋀[R]^r M) ⊗[R] (⋀[R]^s N)),
      ∀ (m : Fin r → M) (n : Fin s → N),
        e.symm ((ιMulti R r m) ⊗ₜ[R] (ιMulti R s n)) =
          ιMulti R (r + s) (Fin.append (fun i ↦ (m i, 0)) (fun j ↦ (0, n j))) := by
  let a := LinearEquiv.ofBijective (directSumMap r s)
    (directSumMap_bijective r s _bM _bN)
  refine ⟨a.symm, ?_, ?_⟩
  · intro m n
    exact directSumMap_ιMulti r s m n
  · intro e he
    have h : e.symm.toLinearMap = a.toLinearMap := by
      apply tensor_wedge_ext r s
      intro m n
      exact (he m n).trans (directSumMap_ιMulti r s m n).symm
    have h' : e.symm = a := LinearEquiv.toLinearMap_injective h
    exact congrArg LinearEquiv.symm h'

/-- The isomorphisms `⋀^(r + s) (M × N) ≃ ⋀^r M ⊗ ⋀^s N` characterised on wedges as in
`exteriorPower.existsUnique_topDirectSum` are natural with respect to isomorphisms
`f : M ≃ M'` and `g : N ≃ N'`. -/
theorem topDirectSum_natural
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    {M' : Type v'} [AddCommGroup M'] [Module R M']
    {N' : Type w'} [AddCommGroup N'] [Module R N']
    (r s : ℕ) (f : M ≃ₗ[R] M') (g : N ≃ₗ[R] N')
    (e : (⋀[R]^(r + s) (M × N)) ≃ₗ[R] ((⋀[R]^r M) ⊗[R] (⋀[R]^s N)))
    (e' : (⋀[R]^(r + s) (M' × N')) ≃ₗ[R] ((⋀[R]^r M') ⊗[R] (⋀[R]^s N')))
    (he : ∀ (m : Fin r → M) (n : Fin s → N),
      e.symm ((ιMulti R r m) ⊗ₜ[R] (ιMulti R s n)) =
        ιMulti R (r + s) (Fin.append (fun i ↦ (m i, 0)) (fun j ↦ (0, n j))))
    (he' : ∀ (m : Fin r → M') (n : Fin s → N'),
      e'.symm ((ιMulti R r m) ⊗ₜ[R] (ιMulti R s n)) =
        ιMulti R (r + s) (Fin.append (fun i ↦ (m i, 0)) (fun j ↦ (0, n j))))
    (x : ⋀[R]^(r + s) (M × N)) :
    e' (map (r + s) (f.toLinearMap.prodMap g.toLinearMap) x) =
      TensorProduct.map (map r f.toLinearMap) (map s g.toLinearMap) (e x) := by
  have h : (map (r + s) (f.toLinearMap.prodMap g.toLinearMap)).comp
      e.symm.toLinearMap = e'.symm.toLinearMap.comp
        (TensorProduct.map (map r f.toLinearMap) (map s g.toLinearMap)) := by
    apply tensor_wedge_ext r s
    intro m n
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, he,
      TensorProduct.map_tmul, map_apply_ιMulti, he']
    congr 1
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp
    · intro j
      simp
  have hx := LinearMap.congr_fun h (e x)
  apply e'.symm.injective
  simpa using hx

end exteriorPower
