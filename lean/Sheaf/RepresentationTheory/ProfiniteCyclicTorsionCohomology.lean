/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.Basic
public import Mathlib.Topology.Instances.ZMod
import WeilConjectures.RepresentationTheory.DiscreteModule.Torsion

/-!
# Torsion cohomology of the profinite integers

Source: main-20261015, `sk-lem-base-field-cd-finite-field.proof.md`, finite cyclic
refinement and vanishing of the inflated norm, and the coinduced resolution of the
continuous-cochain proof. The proof uses finite cyclic partial sums to construct primitives.
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Action

namespace DiscreteModule

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (τ : G) (hdense : DenseRange (fun z : ℤ ↦ τ ^ z))

include hdense

omit [CompactSpace G] in
private theorem eq_top_of_generator {U : Subgroup G} (hU : IsOpen (U : Set G))
    (hτ : τ ∈ U) : U = ⊤ := by
  apply eq_top_iff.mpr
  intro g _
  apply (U.isClosed_of_isOpen hU).closure_subset_iff.mpr
    (show Set.range (fun z : ℤ ↦ τ ^ z) ⊆ U from by
      rintro _ ⟨z, rfl⟩
      exact U.zpow_mem hτ z)
  exact hdense g

omit [CompactSpace G] in
private theorem cyclic_kernel_le (N : ℕ) (χ : G →ₜ* Multiplicative (ZMod N))
    (hχ : χ τ = Multiplicative.ofAdd 1)
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (hτ : τ ^ N ∈ U) :
    χ.toMonoidHom.ker ≤ U := by
  have hc : IsClosed ({g : G | χ g ≠ 1} ∪ (U : Set G)) :=
    ((isOpen_discrete ({1} : Set (Multiplicative (ZMod N)))).preimage
      χ.continuous).isClosed_compl.union (U.isClosed_of_isOpen hU)
  have hr : Set.range (fun z : ℤ ↦ τ ^ z) ⊆ {g : G | χ g ≠ 1} ∪ (U : Set G) := by
    rintro _ ⟨z, rfl⟩
    by_cases hz : χ (τ ^ z) = 1
    · right
      have hz' : (z : ZMod N) = 0 := by
        have h := congrArg Multiplicative.toAdd hz
        simpa [map_zpow, hχ] using h
      obtain ⟨k, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z N).mp hz'
      change τ ^ ((N : ℤ) * k) ∈ U
      rw [zpow_mul, zpow_natCast]
      exact U.zpow_mem hτ k
    · exact Or.inl hz
  intro g hg
  rcases hc.closure_subset_iff.mpr hr (hdense g) with h | h
  · exact (h hg).elim
  · exact h

omit hdense [CompactSpace G] in
private theorem sum_range_periodic {A : Type*} [AddCommGroup A] (F : ℕ → A) (a : ℕ)
    (hF : ∀ m i, F (a * m + i) = F i) (m : ℕ) :
    ∑ i ∈ Finset.range (a * m), F i = m • ∑ i ∈ Finset.range a, F i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [mul_add, mul_one, Finset.sum_range_add, ih, succ_nsmul]
    simp only [hF]

private theorem finite_cyclic_primitive
    (hquot : ∀ N : ℕ, 0 < N → ∃ χ : G →ₜ* Multiplicative (ZMod N),
      χ τ = Multiplicative.ofAdd 1)
    {A : Type*} [AddCommGroup A] (f : G → A)
    (hf : IsOpen (rightStab G f : Set G)) (hA : ∀ x, IsOfFinAddOrder (f x)) :
    ∃ h : G → A, IsOpen (rightStab G h : Set G) ∧ ∀ x, h (x * τ) - h x = f x := by
  classical
  have := Subgroup.quotient_finite_of_isOpen (rightStab G f) hf
  obtain ⟨a, ha, _, haper⟩ := (rightStab G f).exists_pow_mem_of_index_ne_zero
    (rightStab G f).index_ne_zero_of_finite τ
  obtain ⟨e, he, hekill⟩ := exists_pos_nsmul_eq_zero_of_finite
    (finite_range_of_forall_mul_eq f _ hf fun x u hu ↦ hu x)
    (by rintro _ ⟨x, rfl⟩; exact hA x)
  let N := a * e
  have hN : 0 < N := Nat.mul_pos ha he
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  obtain ⟨χ, hχ⟩ := hquot N hN
  have hker : χ.toMonoidHom.ker ≤ rightStab G f :=
    cyclic_kernel_le τ hdense N χ hχ _ hf (by
      change τ ^ (a * e) ∈ rightStab G f
      rw [pow_mul]
      exact (rightStab G f).pow_mem haper e)
  let idx (x : G) := (χ x).toAdd.val
  let F (i : ℕ) := f (τ ^ i)
  have hidx (x : G) : (idx x : ZMod N) = (χ x).toAdd := by
    simpa only [ZMod.cast_id] using (ZMod.natCast_val (R := ZMod N) (χ x).toAdd)
  have key (x : G) : f x = F (idx x) := by
    have hk : x⁻¹ * τ ^ idx x ∈ χ.toMonoidHom.ker := by
      change χ (x⁻¹ * τ ^ idx x) = 1
      apply Multiplicative.toAdd.injective
      simp only [map_mul, map_inv, map_pow, hχ,
        toAdd_mul, toAdd_inv, toAdd_pow,
        toAdd_ofAdd, toAdd_one, nsmul_one]
      rw [hidx, neg_add_cancel]
    have hh := hker hk x
    simpa [F] using hh.symm
  have hperiod (m i : ℕ) : F (a * m + i) = F i := by
    have hmem : τ ^ (a * m) ∈ rightStab G f := by
      rw [pow_mul]
      exact (rightStab G f).pow_mem haper m
    have hh := hmem (τ ^ i)
    simpa only [F, ← pow_add, Nat.add_comm i] using hh
  have hsum : ∑ i ∈ Finset.range N, F i = 0 := by
    rw [sum_range_periodic F a hperiod, Finset.smul_sum]
    exact Finset.sum_eq_zero fun i _ ↦ hekill _ ⟨τ ^ i, rfl⟩
  let h (x : G) := ∑ i ∈ Finset.range (idx x), F i
  have hidxk (x k : G) (hk : k ∈ χ.toMonoidHom.ker) : idx (x * k) = idx x := by
    change (χ (x * k)).toAdd.val = _
    rw [map_mul, show χ k = 1 from hk, mul_one]
  refine ⟨h, ?_, fun x ↦ ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := χ.toMonoidHom.ker) ?_
      ((isOpen_discrete {1}).preimage χ.continuous)
    intro k hk
    change ∀ x, h (x * k) = h x
    intro x
    exact congrArg (fun i ↦ ∑ j ∈ Finset.range i, F j) (hidxk x k hk)
  · have hidxτ : idx (x * τ) = (idx x + 1) % N := by
      simp only [idx, map_mul, hχ, toAdd_mul,
        toAdd_ofAdd]
      rw [ZMod.val_add]
      by_cases hN1 : N = 1
      · simp only [hN1, Nat.mod_one]
      · rw [ZMod.val_one'' hN1]
    have hlt : idx x < N := ZMod.val_lt _
    change (∑ i ∈ Finset.range (idx (x * τ)), F i) -
      (∑ i ∈ Finset.range (idx x), F i) = _
    rcases Nat.lt_or_ge (idx x + 1) N with hsmall | hlarge
    · rw [hidxτ, Nat.mod_eq_of_lt hsmall, Finset.sum_range_succ,
        add_sub_cancel_left, ← key x]
    · have heq : idx x + 1 = N := by omega
      rw [← heq, Finset.sum_range_succ, ← key x] at hsum
      rw [hidxτ, heq, Nat.mod_self, Finset.sum_range_zero, zero_sub]
      exact neg_eq_iff_eq_neg.mpr (eq_neg_of_add_eq_zero_left hsum)

omit [CompactSpace G] in
private theorem subsingleton_H_one_of_surjective
    (X : DiscreteModule.{w} G)
    (hsurj : ∀ x : X.obj.V, ∃ y : X.obj.V, (X.obj.ρ τ).hom y - y = x) :
    Subsingleton (H G X 1) := by
  change Subsingleton (Abelian.Ext (intTrivial G) (shortComplex₁ X).X₁ 1)
  rw [subsingleton_ext_one_iff (shortExact₁ X) (subsingleton_H_coind₁ _ 0),
    forall_exists_comp_eq_iff]
  intro z hz
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hτf : (((coind₁ G).obj X.obj.V).obj.ρ τ).hom f - f ∈ toCoind₁Range X := by
    rw [← QuotientAddGroup.eq_iff_sub_mem]
    exact hz τ
  obtain ⟨x, hx⟩ := hτf
  obtain ⟨y, hy⟩ := hsurj x
  let f' := f - (toCoind₁ X).hom.hom.hom y
  have hf' : (((coind₁ G).obj X.obj.V).obj.ρ τ).hom f' = f' := by
    have h1 : (((coind₁ G).obj X.obj.V).obj.ρ τ).hom f =
        f + (toCoind₁ X).hom.hom.hom x := by rw [hx]; abel
    simp only [f', map_sub, h1, ← hom_comm_apply, ← hy, map_sub]
    abel
  have htop := eq_top_of_generator τ hdense
    (((coind₁ G).obj X.obj.V).isOpen_stabilizer f') hf'
  refine ⟨f', fun g ↦ ?_, ?_⟩
  · have hg : g ∈ ((coind₁ G).obj X.obj.V).obj.stabilizer f' :=
      htop ▸ Subgroup.mem_top g
    exact hg
  · have h0 : (QuotientAddGroup.mk ((toCoind₁ X).hom.hom.hom y) :
        (coker₁ X).obj.V) = 0 := (QuotientAddGroup.eq_zero_iff _).mpr ⟨y, rfl⟩
    simp only [shortComplex₁, coker₁π_apply, f', QuotientAddGroup.mk_sub, h0, sub_zero]

/-- A compact group with a dense integer generator and cyclic quotients of every positive
order has no torsion cohomology above degree one.

Source: main-20261015, `sk-lem-base-field-cd-finite-field.proof.md`, finite-module
paragraph, and `sk-lem-base-field-cd.proof.md`, continuous-cochain paragraph.
(blueprint: lem-base-field-profinite-cyclic-torsion-cohomology)

Proof: A smooth function has finite image and a finite period a along the generator.
Choose a positive exponent e killing its image. At the cyclic quotient of order ae,
its sum around the cycle is e times its sum around the period a, hence zero. Partial
sums therefore give a smooth primitive for translation minus identity, including the
wraparound equation. Density shows that the kernel of this quotient fixes the function:
the claim holds on integer powers and extends across a clopen set. Thus translation
minus identity is surjective on the quotient of the coinduced module by the original
torsion module. An invariant class in the next coinduced quotient lifts to an invariant
function after subtracting the orbit function of such a primitive; being fixed by the
generator implies invariance under the whole compact group. The coinduced short exact
sequence then gives H² = 0. Its quotient is torsion, since a smooth function has finite
image. Dimension shifting repeats the argument for all higher degrees. -/
theorem subsingleton_H_of_dense_generator_cyclic_quotients
    (hquot : ∀ N : ℕ, 0 < N → ∃ χ : G →ₜ* Multiplicative (ZMod N),
      χ τ = Multiplicative.ofAdd 1)
    (X : DiscreteModule.{w} G) (hX : ∀ x : X.obj.V, IsOfFinAddOrder x)
    {q : ℕ} (hq : 2 ≤ q) : Subsingleton (H G X q) := by
  have htwo (M : DiscreteModule.{w} G) (hM : ∀ x : M.obj.V, IsOfFinAddOrder x) :
      Subsingleton (H G M 2) := by
    have hs : ∀ z : (coker₁ M).obj.V, ∃ y : (coker₁ M).obj.V,
        ((coker₁ M).obj.ρ τ).hom y - y = z := by
      intro z
      obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective z
      obtain ⟨h, hh, heq⟩ := finite_cyclic_primitive τ hdense hquot f.1 f.2 fun x ↦ hM _
      let h' : ((coind₁ G).obj M.obj.V).obj.V := ⟨h, hh⟩
      refine ⟨QuotientAddGroup.mk h', ?_⟩
      rw [coker₁_ρ_mk, ← QuotientAddGroup.mk_sub]
      congr 1
      exact Subtype.ext (funext heq)
    exact subsingleton_ext_succ_of_shortExact (shortExact₁ M) (subsingleton_H_coind₁ _ 1)
      (subsingleton_H_one_of_surjective τ hdense (coker₁ M) hs)
  induction q, hq using Nat.le_induction generalizing X with
  | base => exact htwo X hX
  | succ n hn ih =>
    exact subsingleton_ext_succ_of_shortExact (shortExact₁ X) (subsingleton_H_coind₁ _ n)
      (ih _ (isOfFinAddOrder_coker₁ hX))

end DiscreteModule
