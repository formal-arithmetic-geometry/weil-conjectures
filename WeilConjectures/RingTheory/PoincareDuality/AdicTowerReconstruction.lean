/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Reconstruction from an adic tower

An inverse limit `L` of a tower of modules `N n` over `A / I^(n+1)`, with `I` finitely generated
and transitions inducing `N (n+1) / I^(n+1) ≅ N n`, is `I`-adically complete with
`L / I^(n+1) L ≅ N n`.

## Implementation details

Here `N n` denotes `M_{n+1}` in the Stacks Project. The canonical map from `L` to its completion
has a left inverse, so `L` is complete as a retract of a complete module (Tags 05GG, 09B7). The
kernels `K n = ker (p n)` then satisfy `K n = I^(n+1) L`, since the inverse limit of the
surjective tower `K n / (K n ∩ I^(n+1) L)` vanishes.

## References

* [Stacks, Tag 09B8]
* [Stacks, Tag 09B7]
* [Stacks, Tag 05GG]
-/

@[expose] public section

universe u v w

namespace Ideal

private theorem tower_lift (N : ℕ → Type v) (t : ∀ n, N (n + 1) → N n)
    (ht : ∀ n, Function.Surjective (t n)) (k : ℕ) (x : N k) :
    ∃ y : ∀ n, N n, (∀ n, t n (y (n + 1)) = y n) ∧ y k = x := by
  classical
  induction k generalizing N with
  | zero =>
    let y : ∀ n, N n := Nat.rec x (fun n z ↦ (ht n z).choose)
    exact ⟨y, fun n ↦ (ht n (y n)).choose_spec, rfl⟩
  | succ k ih =>
    obtain ⟨y, hy, hx⟩ := ih (fun n ↦ N (n + 1)) (fun n ↦ t (n + 1))
      (fun n ↦ ht (n + 1)) x
    let z : ∀ n, N n := fun n ↦ match n with
      | 0 => t 0 (y 0)
      | n + 1 => y n
    refine ⟨z, ?_, hx⟩
    intro n
    cases n with
    | zero => rfl
    | succ n => exact hy n

private theorem map_pow_mem {A : Type u} [CommRing A] (I : Ideal A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {L : Type w} [AddCommGroup L] [Module A L] (f : M →ₗ[A] L)
    (n : ℕ) {x : M} (hx : x ∈ (I ^ n • ⊤ : Submodule A M)) :
    f x ∈ (I ^ n • ⊤ : Submodule A L) := by
  have h : Submodule.map f (I ^ n • ⊤) ≤ (I ^ n • ⊤ : Submodule A L) := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ le_top
  exact h (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)

/-- Let `I` be a finitely generated ideal and `N n` a tower of `A`-modules annihilated by
`I^(n+1)` with surjective transitions whose kernels are `I^(n+1) N (n+1)`. If `L` is the inverse
limit of the tower via the maps `p`, then `p n` induces `L / I^(n+1) L ≃ N n`, `L` is `I`-adically
complete and Hausdorff, and the inverse-limit topology on `L` is the `I`-adic topology. -/
theorem adic_tower_reconstruction
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (N : ℕ → Type v) [∀ n, AddCommGroup (N n)] [∀ n, Module A (N n)]
    (t : ∀ n, N (n + 1) →ₗ[A] N n)
    (hN : ∀ n, (I ^ (n + 1) • ⊤ : Submodule A (N n)) = ⊥)
    (ht : ∀ n, Function.Surjective (t n) ∧
      (t n).ker = (I ^ (n + 1) • ⊤ : Submodule A (N (n + 1))))
    (L : Type w) [AddCommGroup L] [Module A L]
    (p : ∀ n, L →ₗ[A] N n)
    (hp : ∀ n, (t n).comp (p (n + 1)) = p n)
    (hlim : ∀ x : ∀ n, N n, (∀ n, t n (x (n + 1)) = x n) →
      ∃! y : L, ∀ n, p n y = x n) :
    (∀ n, ∃ e : (L ⧸ (I ^ (n + 1) • ⊤ : Submodule A L)) ≃ₗ[A] N n,
      ∀ y : L, e ((I ^ (n + 1) • ⊤ : Submodule A L).mkQ y) = p n y) ∧
    IsAdicComplete I L ∧ IsHausdorff I L ∧
    (⨅ n, TopologicalSpace.induced (p n) (⊥ : TopologicalSpace (N n))) =
      I.adicModuleTopology L := by
  classical
  have hp_apply (n : ℕ) (x : L) : t n (p (n + 1) x) = p n x :=
    LinearMap.congr_fun (hp n) x
  have hext {x y : L} (h : ∀ n, p n x = p n y) : x = y := by
    obtain ⟨z, hz, hu⟩ := hlim (fun n ↦ p n y) (fun n ↦ hp_apply n y)
    exact (hu x h).trans (hu y (fun _ ↦ rfl)).symm
  have hkill (n : ℕ) : (I ^ (n + 1) • ⊤ : Submodule A L) ≤ (p n).ker := by
    intro x hx
    have hm := map_pow_mem I (p n) (n + 1) hx
    rw [hN n] at hm
    exact hm
  let q (n : ℕ) : (L ⧸ (I ^ (n + 1) • ⊤ : Submodule A L)) →ₗ[A] N n :=
    Submodule.liftQ _ (p n) (hkill n)
  have hq (n : ℕ) (x : L) : q n (Submodule.Quotient.mk x) = p n x := rfl
  have hqc (n : ℕ) (x : L ⧸ (I ^ (n + 1 + 1) • ⊤ : Submodule A L)) :
      t n (q (n + 1) x) =
        q n (Submodule.factorPow I L (Nat.le_succ (n + 1)) x) := by
    induction x using Submodule.Quotient.induction_on
    exact hp_apply n _
  let C := AdicCompletion I L
  let f (n : ℕ) : C →ₗ[A] N n := (q n).comp (AdicCompletion.eval I L (n + 1))
  have hf (x : C) (n : ℕ) : t n (f (n + 1) x) = f n x := by
    change t n (q (n + 1) (x.val (n + 1 + 1))) = q n (x.val (n + 1))
    rw [hqc]
    exact congrArg (q n) (x.property (Nat.le_succ (n + 1)))
  let g (x : C) : L := (hlim (fun n ↦ f n x) (hf x)).choose
  have hg (n : ℕ) (x : C) : p n (g x) = f n x :=
    (hlim (fun n ↦ f n x) (hf x)).choose_spec.1 n
  let r : C →ₗ[A] L :=
    { toFun := g
      map_add' := fun x y ↦ hext (fun n ↦ by simp only [map_add, hg])
      map_smul' := fun a x ↦ hext (fun n ↦ by
        simp only [map_smul, hg, RingHom.id_apply]) }
  have hr (n : ℕ) (x : C) : p n (r x) = f n x := hg n x
  have hrc (x : L) : r (AdicCompletion.of I L x) = x := by
    apply hext
    intro n
    rw [hr]
    rfl
  have : IsAdicComplete I C := AdicCompletion.isAdicComplete hI
  have : IsHausdorff I L := ⟨fun x hx ↦ by
    apply hext
    intro n
    rw [map_zero]
    exact hkill n ((SModEq.zero.mp (hx (n + 1))))⟩
  have : IsPrecomplete I L := ⟨fun x hx ↦ by
    obtain ⟨z, hz⟩ := IsPrecomplete.prec' (I := I)
      (fun n ↦ AdicCompletion.of I L (x n)) (fun {m n} hmn ↦ by
        apply SModEq.sub_mem.mpr
        rw [← map_sub]
        exact map_pow_mem I (AdicCompletion.of I L) m (SModEq.sub_mem.mp (hx hmn)))
    refine ⟨r z, fun n ↦ SModEq.sub_mem.mpr ?_⟩
    rw [← hrc (x n), ← map_sub]
    exact map_pow_mem I r n (SModEq.sub_mem.mp (hz n))⟩
  have : IsAdicComplete I L := ⟨⟩
  have hrinj : Function.Injective r := by
    intro x y h
    obtain ⟨x, rfl⟩ := AdicCompletion.of_surjective I L x
    obtain ⟨y, rfl⟩ := AdicCompletion.of_surjective I L y
    rw [hrc, hrc] at h
    exact congrArg (AdicCompletion.of I L) h
  have hps (n : ℕ) : Function.Surjective (p n) := by
    intro x
    obtain ⟨y, hy, hx⟩ := tower_lift N (fun n ↦ t n) (fun n ↦ (ht n).1) n x
    obtain ⟨z, hz, _⟩ := hlim y hy
    exact ⟨z, (hz n).trans hx⟩
  let K (n : ℕ) := (q n).ker
  let s (n : ℕ) : K (n + 1) → K n := fun x ↦
    ⟨Submodule.factorPow I L (Nat.le_succ (n + 1)) x.val, by
      change q n _ = 0
      rw [← hqc]
      exact (t n).map_zero ▸ congrArg (t n) x.property⟩
  have hs (n : ℕ) : Function.Surjective (s n) := by
    intro a
    obtain ⟨x, hx⟩ := (I ^ (n + 1) • ⊤ : Submodule A L).mkQ_surjective a.val
    have hpx : p n x = 0 := by
      change Submodule.Quotient.mk x = a.val at hx
      rw [← hq, hx]
      exact a.property
    have hz : p (n + 1) x ∈
        (I ^ (n + 1) • ⊤ : Submodule A (N (n + 1))) := by
      rw [← (ht n).2, LinearMap.mem_ker, hp_apply, hpx]
    have hm : Submodule.map (p (n + 1)) (I ^ (n + 1) • ⊤) =
        (I ^ (n + 1) • ⊤ : Submodule A (N (n + 1))) := by
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr (hps (n + 1))]
    rw [← hm] at hz
    obtain ⟨u, hu, he⟩ := Submodule.mem_map.mp hz
    let b : K (n + 1) := ⟨Submodule.Quotient.mk (x - u), by
      change p (n + 1) (x - u) = 0
      rw [map_sub, he, sub_self]⟩
    refine ⟨b, Subtype.ext ?_⟩
    change (I ^ (n + 1) • ⊤ : Submodule A L).mkQ (x - u) = a.val
    have hu0 : (I ^ (n + 1) • ⊤ : Submodule A L).mkQ u = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hu
    rw [map_sub, hu0, sub_zero, hx]
  have hqi (n : ℕ) : Function.Injective (q n) := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm _ bot_le
    intro a ha
    obtain ⟨y, hy, hyn⟩ := tower_lift (fun k ↦ ↥(K k)) s hs n ⟨a, ha⟩
    let z : ∀ n, L ⧸ (I ^ n • ⊤ : Submodule A L) := fun n ↦ match n with
      | 0 => 0
      | n + 1 => (y n).val
    have hzs (n : ℕ) : z n =
        Submodule.factorPow I L (Nat.le_succ n) (z (n + 1)) := by
      cases n with
      | zero =>
        have : Subsingleton (L ⧸ (I ^ 0 • ⊤ : Submodule A L)) := by
          simp only [pow_zero, one_smul]
          infer_instance
        exact Subsingleton.elim _ _
      | succ n => exact (congrArg Subtype.val (hy n)).symm
    let c : C := ⟨z, fun {m n} hmn ↦
      (Submodule.eq_factor_of_eq_factor_succ
        (fun _ _ h ↦ Submodule.pow_smul_top_le I L h) z hzs hmn).symm⟩
    have hcz : r c = 0 := by
      apply hext
      intro k
      rw [hr, map_zero]
      exact (y k).property
    have hc : c = 0 := hrinj (by rw [hcz, map_zero])
    have he : (y n).val = 0 := congrArg (fun c : C ↦ c.val (n + 1)) hc
    rw [congrArg Subtype.val hyn] at he
    exact he
  have hquot (n : ℕ) :
      ∃ e : (L ⧸ (I ^ (n + 1) • ⊤ : Submodule A L)) ≃ₗ[A] N n,
        ∀ y : L, e ((I ^ (n + 1) • ⊤ : Submodule A L).mkQ y) = p n y := by
    have hqs : Function.Surjective (q n) := by
      intro x
      obtain ⟨y, rfl⟩ := hps n x
      exact ⟨Submodule.Quotient.mk y, rfl⟩
    exact ⟨LinearEquiv.ofBijective (q n) ⟨hqi n, hqs⟩, fun _ ↦ rfl⟩
  have hk (n : ℕ) : (p n).ker = (I ^ (n + 1) • ⊤ : Submodule A L) := by
    apply le_antisymm _ (hkill n)
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply hqi n
    simpa only [hq, map_zero] using (show p n x = 0 from hx)
  refine ⟨hquot, inferInstance, inferInstance, ?_⟩
  let : ∀ n, TopologicalSpace (N n) := fun _ ↦ ⊥
  have : ∀ n, DiscreteTopology (N n) := fun _ ↦ ⟨rfl⟩
  let : TopologicalSpace A := I.adicTopology
  let B := I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis L)
  have hb : Filter.HasBasis (@nhds L (I.adicModuleTopology L) 0)
      (fun _ : ℕ ↦ True) (fun n ↦ (I ^ n • ⊤ : Submodule A L) : ℕ → Set L) := by
    constructor
    intro U
    rw [B.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨V, ⟨n, rfl⟩, h⟩
      exact ⟨n, trivial, h⟩
    · rintro ⟨n, _, h⟩
      exact ⟨_, ⟨n, rfl⟩, h⟩
  apply IsTopologicalAddGroup.ext
  · apply isTopologicalAddGroup_iInf
    intro n
    exact isTopologicalAddGroup_induced (p n).toAddMonoidHom
  · let := I.adicModuleTopology L
    infer_instance
  · rw [nhds_iInf, hb.eq_iInf]
    have hn (n : ℕ) :
        @nhds L (TopologicalSpace.induced (p n) (⊥ : TopologicalSpace (N n))) 0 =
          Filter.principal ((I ^ (n + 1) • ⊤ : Submodule A L) : Set L) := by
      rw [nhds_induced, map_zero, nhds_discrete, Filter.comap_pure]
      congr 1
      exact congrArg (fun K : Submodule A L ↦ (K : Set L)) (hk n)
    simp_rw [hn]
    apply le_antisymm
    · apply le_iInf
      intro n
      exact (iInf_le_of_le n (Filter.principal_mono.mpr
        (Submodule.pow_smul_top_le I L (Nat.le_succ n))))
    · apply le_iInf
      intro n
      exact iInf_le_of_le (n + 1) le_rfl

end Ideal
