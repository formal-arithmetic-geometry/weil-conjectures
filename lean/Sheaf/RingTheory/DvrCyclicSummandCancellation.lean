/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Cancellation of a cyclic summand over a discrete valuation ring

Source: the agent scalar calculation accompanying Hemo--Richarz--Scholbach,
Example 3.1 and Theorem 6.12(2), extracted from the local Smith argument;
Stacks Project, Algebra, Tag 00E9 supplies the local-ring unit criterion
(blueprint: lem-sfb-dvr-cyclic-summand-cancellation).

A binary direct sum is represented by the product of its two modules, with
componentwise operations, as in the node's proof. Ideal quotients are the
corresponding submodule quotients. No basis or freeness is assumed.
-/

@[expose] public section

universe u v w z

namespace IsDiscreteValuationRing

private theorem cancel_of_fst_equiv
    {A : Type u} [CommRing A] {C : Type z} {M : Type v} {N : Type w}
    [AddCommGroup C] [AddCommGroup M] [AddCommGroup N]
    [Module A C] [Module A M] [Module A N]
    (F : (C × M) ≃ₗ[A] (C × N)) (p : C ≃ₗ[A] C)
    (hp : ∀ x, (F (x, 0)).1 = p x) : Nonempty (M ≃ₗ[A] N) := by
  let b : M →ₗ[A] C := (LinearMap.fst A C N).comp
    (F.toLinearMap.comp (LinearMap.inr A C M))
  let S : (C × M) ≃ₗ[A] (C × M) :=
    ((LinearEquiv.prodComm A C M).trans
      ((LinearEquiv.refl A M).skewProd (LinearEquiv.refl A C)
        (-p.symm.toLinearMap.comp b))).trans (LinearEquiv.prodComm A M C)
  let D := S.trans F
  have hF (x : C) (m : M) : (F (x, m)).1 = p x + b m := by
    have hpair : (x, m) = (x, 0) + (0, m) := by simp
    rw [hpair, map_add, Prod.fst_add, hp]
    rfl
  have hD (x : C) (m : M) : (D (x, m)).1 = p x := by
    change (F (x + -(p.symm (b m)), m)).1 = p x
    rw [hF]
    simp
  let f : M →ₗ[A] N := (LinearMap.snd A C N).comp
    (D.toLinearMap.comp (LinearMap.inr A C M))
  refine ⟨LinearEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro m₁ m₂ hm
    have heq : D (0, m₁) = D (0, m₂) := by
      apply Prod.ext
      · rw [hD, hD]
      · exact hm
    exact congrArg Prod.snd (D.injective heq)
  · intro n
    obtain ⟨⟨x, m⟩, hm⟩ := D.surjective (0, n)
    have hx : x = 0 := p.injective (by
      simpa only [hD, map_zero] using congrArg Prod.fst hm)
    refine ⟨m, ?_⟩
    subst x
    exact congrArg Prod.snd hm

private theorem quotient_end_scalar
    {A : Type u} [CommRing A] (I : Ideal A) (f : (A ⧸ I) →ₗ[A] (A ⧸ I)) :
    ∃ u : A, ∀ x, f x = u • x := by
  obtain ⟨u, hu⟩ := I.mkQ_surjective (f (I.mkQ 1))
  refine ⟨u, ?_⟩
  intro x
  obtain ⟨t, rfl⟩ := I.mkQ_surjective x
  have ht : I.mkQ t = t • I.mkQ 1 := by rw [← map_smul]; simp
  calc
    f (I.mkQ t) = t • f (I.mkQ 1) := by rw [ht, map_smul]
    _ = t • I.mkQ u := by rw [hu]
    _ = I.mkQ (t * u) := (map_smul I.mkQ t u).symm
    _ = I.mkQ (u * t) := congrArg I.mkQ (mul_comm t u)
    _ = u • I.mkQ t := map_smul I.mkQ u t

/-- Cancel the common summand `A / (π^e)` from an isomorphism of finitely generated
`A`-modules. The exponent may be zero.

Source: agent scalar calculation accompanying Hemo--Richarz--Scholbach, Example 3.1
and Theorem 6.12(2), extracted from the local Smith argument; Stacks Project,
Algebra, Tag 00E9 for the unit criterion
(blueprint: lem-sfb-dvr-cyclic-summand-cancellation).

Proof plan (the node's four steps):
1. If `e = 0`, the quotient is zero and the given equivalence identifies `M` and `N`.
   Otherwise put `C = A / (π^e)`. Write the equivalence and its inverse in blocks
   `F = (a,b;c,d)` and `G = (a',b';c',d')`. Since `C` is cyclic, `a` and `a'` are
   multiplication by representatives `u,v` in `A`. The first block of `GF = 1`
   gives `b'c = 1 - vu`.
2. The maximal ideal is `πA`. By `IsLocalRing.notMem_maximalIdeal` (the node
   `lem-weil-pbc-local-ring-unit-criterion`), if `u` is outside it, `a` is invertible.
   Otherwise `w = 1 + (1-v)u` is outside it and is a unit. Postcompose `F` with
   the shear `(x,n) ↦ (x+b'(n),n)`, whose inverse subtracts `b'(n)`. The new
   upper-left block is multiplication by `w`. Thus obtain `F₁ = (p,q;r,s)` with
   `p` invertible.
3. Precompose with `(x,m) ↦ (x-p⁻¹q(m),m)` and postcompose with
   `(x,n) ↦ (x,n-rp⁻¹(x))`. Replacing minus by plus gives the inverse shears.
   Direct substitution gives the diagonal equivalence `D(x,m) = (p(x),h(m))`,
   where `h = s-rp⁻¹q`. Its inverse `J` is the composite of the known inverses.
4. Define `t(n)` as the second component of `J(0,n)`. The second components of
   `DJ(0,n) = (0,n)` and `JD(0,m) = (0,m)` give `h(t(n)) = n` and `t(h(m)) = m`.
   These linear maps give the required equivalence. All operations are operations
   on pairs; neither freeness nor a basis is used. -/
theorem nonempty_linearEquiv_of_cyclic_prod
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π}) (e : ℕ)
    (M : Type v) (N : Type w) [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N] [Module.Finite A M] [Module.Finite A N]
    (h : Nonempty (((A ⧸ Ideal.span {π ^ e}) × M) ≃ₗ[A]
      ((A ⧸ Ideal.span {π ^ e}) × N))) :
    Nonempty (M ≃ₗ[A] N) := by
  classical
  have _hπ : IsLocalRing.maximalIdeal A = Ideal.span {π} := hπ
  clear _hπ
  obtain ⟨F⟩ := h
  let I := Ideal.span {π ^ e}
  let C := A ⧸ I
  let a : C →ₗ[A] C := (LinearMap.fst A C N).comp
    (F.toLinearMap.comp (LinearMap.inl A C M))
  let a' : C →ₗ[A] C := (LinearMap.fst A C M).comp
    (F.symm.toLinearMap.comp (LinearMap.inl A C N))
  let b' : N →ₗ[A] C := (LinearMap.fst A C M).comp
    (F.symm.toLinearMap.comp (LinearMap.inr A C N))
  obtain ⟨u, hu⟩ := quotient_end_scalar I a
  obtain ⟨v, hv⟩ := quotient_end_scalar I a'
  have hF (x : C) : (F (x, 0)).1 = u • x := hu x
  have hG (x : C) (n : N) : (F.symm (x, n)).1 = v • x + b' n := by
    have hpair : (x, n) = (x, 0) + (0, n) := by simp
    rw [hpair, map_add, Prod.fst_add]
    change a' x + b' n = v • x + b' n
    rw [hv]
  have hbc (x : C) : b' (F (x, 0)).2 = x - v • (u • x) := by
    have hid := congrArg Prod.fst (F.symm_apply_apply (x, 0))
    rw [hG, hF] at hid
    exact eq_sub_of_add_eq' hid
  by_cases hunit : IsUnit u
  · obtain ⟨u₀, hu₀⟩ := hunit
    apply cancel_of_fst_equiv F (LinearEquiv.smulOfUnit u₀)
    intro x
    change (F (x, 0)).1 = (u₀ : A) • x
    rw [hu₀]
    exact hF x
  · have hw : IsUnit (1 + (1 - v) * u) := by
      apply IsLocalRing.notMem_maximalIdeal.mp
      intro hw
      have humem : u ∈ IsLocalRing.maximalIdeal A := by
        by_contra humem
        exact hunit (IsLocalRing.notMem_maximalIdeal.mp humem)
      have hprod := (IsLocalRing.maximalIdeal A).mul_mem_left (1 - v) humem
      have hone : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
        simpa only [add_sub_cancel_right] using
          (IsLocalRing.maximalIdeal A).sub_mem hw hprod
      exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) hone
    let H : (C × N) ≃ₗ[A] (C × N) :=
      ((LinearEquiv.prodComm A C N).trans
        ((LinearEquiv.refl A N).skewProd (LinearEquiv.refl A C) b')).trans
          (LinearEquiv.prodComm A N C)
    have hHF (x : C) : ((F.trans H) (x, 0)).1 = (1 + (1 - v) * u) • x := by
      change (F (x, 0)).1 + b' (F (x, 0)).2 = _
      rw [hF, hbc]
      simp only [add_smul, sub_smul, one_smul, mul_smul]
      abel
    obtain ⟨w₀, hw₀⟩ := hw
    apply cancel_of_fst_equiv (F.trans H) (LinearEquiv.smulOfUnit w₀)
    intro x
    change ((F.trans H) (x, 0)).1 = (w₀ : A) • x
    rw [hw₀]
    exact hHF x

end IsDiscreteValuationRing
