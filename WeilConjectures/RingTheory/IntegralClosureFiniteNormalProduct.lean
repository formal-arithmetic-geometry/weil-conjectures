/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.FiniteProductNormal

/-!
# Integral closure in a finite product of normal domains

## References

* [Stacks, Tag 035L]
* [Stacks, Tag 034L]
-/

@[expose] public section

universe u v w

open Polynomial

private theorem integral_pi {A : Type u} [CommRing A] {ι : Type v} [Finite ι]
    {B : ι → Type w} [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    (x : ∀ i, B i) (hx : ∀ i, IsIntegral A (x i)) : IsIntegral A x := by
  classical
  let := Fintype.ofFinite ι
  choose p hp hz using hx
  refine ⟨∏ i, p i, monic_prod_of_monic _ _ (fun i _ ↦ hp i), ?_⟩
  change aeval x (∏ i, p i) = 0
  ext i
  rw [aeval_pi_apply₂, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa [aeval_def] using hz i)

/-- The integral closure of `A` in a finite product of normal domains has normal prime
localizations. -/
theorem integralClosure_normal_localizations_of_finite_product
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type v} [Finite ι] (C : ι → Type u) [∀ i, CommRing (C i)]
    [∀ i, IsDomain (C i)] [∀ i, IsIntegrallyClosed (C i)]
    (e : B ≃+* ∀ i, C i) (p : Ideal (integralClosure A B)) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  classical
  let (i : ι) : Algebra A (C i) :=
    ((Pi.evalRingHom C i).comp (e.toRingHom.comp (algebraMap A B))).toAlgebra
  let ea : B ≃ₐ[A] (∀ i, C i) :=
    { e with commutes' := fun a ↦ rfl }
  let g : integralClosure A B →+* ∀ i, integralClosure A (C i) :=
    { toFun := fun x i ↦ ⟨e x i, x.property.map ((Pi.evalAlgHom A C i).comp ea.toAlgHom)⟩
      map_one' := by ext i; exact congrFun e.map_one i
      map_mul' := by intro x y; ext i; exact congrFun (e.map_mul x y) i
      map_zero' := by ext i; exact congrFun e.map_zero i
      map_add' := by intro x y; ext i; exact congrFun (e.map_add x y) i }
  have hg : Function.Bijective g := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply e.injective
      funext i
      exact congrArg Subtype.val (congrFun h i)
    · intro x
      have hx : IsIntegral A (fun i ↦ (x i : C i)) :=
        integral_pi _ (fun i ↦ (x i).property)
      refine ⟨⟨e.symm (fun i ↦ (x i : C i)), hx.map ea.symm.toAlgHom⟩, ?_⟩
      ext i
      exact congrFun (e.apply_symm_apply _) i
  let ec := RingEquiv.ofBijective g hg
  let q : Ideal (∀ i, integralClosure A (C i)) := p.map ec.toRingHom
  let : q.IsPrime := Ideal.map_isPrime_of_equiv ec
  have hpq : p = q.comap ec.toRingHom := by
    exact (p.comap_map_of_bijective ec.toRingHom ec.bijective).symm
  have hn (i : ι) (r : Ideal (integralClosure A (C i))) [r.IsPrime] :
      IsDomain (Localization.AtPrime r) ∧ IsIntegrallyClosed (Localization.AtPrime r) := by
    let : IsIntegrallyClosed (integralClosure A (C i)) :=
      .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ (C i)
    exact ⟨inferInstance,
      isIntegrallyClosed_of_isLocalization _ _ r.primeCompl_le_nonZeroDivisors⟩
  obtain ⟨hd, hi⟩ := Pi.isNormalRing_of_finite (fun i ↦ integralClosure A (C i)) hn q
  let : IsDomain (Localization.AtPrime q) := hd
  let : IsIntegrallyClosed (Localization.AtPrime q) := hi
  let ep := Localization.localRingEquiv p q ec hpq
  exact ⟨ep.toMulEquiv.isDomain, IsIntegrallyClosed.of_equiv ep.symm⟩
