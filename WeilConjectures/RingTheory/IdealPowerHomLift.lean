/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.AlgebraicGeometry.TorsionModuleFlatBaseChangeIso
import WeilConjectures.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Lifting maps from an ideal power modulo principal maps

Let `R → S` be flat with `R/I ≃ S/IS` and `I` finitely generated. Every `R`-linear map
`I^n → S ⊗[R] N` agrees, up to a principal map `r ↦ r • m`, with the scalar extension of an
`R`-linear map `I^n → N`.

## Implementation details

Finite Koszul one-cycles of generators of `I^n` lift modulo principal cycles: the one-cycle
homology is killed by `I^n`, so its base change to `S` is bijective by the ideal-power torsion
comparison. The lifted cycle defines a map vanishing on the relations among the generators,
which therefore factors through `I^n`.

## References

* [Stacks, Tag 05ED]
* [Stacks, Tag 05EE]
* [Stacks, Tag 05EF]
* [Stacks, Tag 05EG]
* [Stacks, Tag 05E9]
* [Stacks, Tag 05EC]
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace LinearMap

/-- Finite Koszul one-cycles lift modulo principal cycles over a flat neighbourhood: for
generators `fᵢ` of `I^n`, every tuple `xᵢ` in `S ⊗[R] N` with `fᵢ xⱼ = fⱼ xᵢ` differs from the
image of such a tuple over `N` by a principal tuple `(fᵢ m)`. -/
private theorem exists_finite_koszul_cycle_lift
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (_hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (n : ℕ) (hn : 1 ≤ n) (s : Finset R)
    (_hs : Ideal.span (s : Set R) = I ^ n)
    {N : Type w} [AddCommGroup N] [Module R N]
    (x : s → S ⊗[R] N)
    (_hx : ∀ i j : s, (i : R) • x j = (j : R) • x i) :
    ∃ (y : s → N) (m : S ⊗[R] N),
      (∀ i j : s, (i : R) • y j = (j : R) • y i) ∧
      ∀ i : s, 1 ⊗ₜ[R] y i = x i + (i : R) • m := by
  classical
  let : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  let δ : (s → N) →ₗ[R] (s × s → N) :=
    LinearMap.pi fun ij ↦
      (ij.1 : R) • LinearMap.proj ij.2 - (ij.2 : R) • LinearMap.proj ij.1
  let Z := LinearMap.ker δ
  let b₀ : N →ₗ[R] (s → N) := LinearMap.pi fun i ↦ (i : R) • LinearMap.id
  have hb₀ : ∀ a : N, b₀ a ∈ Z := by
    intro a
    change δ (b₀ a) = 0
    ext ij
    simp [δ, b₀, smul_smul, mul_comm]
  let b : N →ₗ[R] Z := b₀.codRestrict Z hb₀
  let H := Z ⧸ LinearMap.range b
  let q : Z →ₗ[R] H := (LinearMap.range b).mkQ
  have hcyc : ∀ z : Z, ∀ i j : s, (i : R) • (z : s → N) j =
      (j : R) • (z : s → N) i := by
    intro z i j
    have hz := congrFun (LinearMap.mem_ker.mp z.property) (i, j)
    exact sub_eq_zero.mp hz
  have hkill : ∀ h : H, ∀ r ∈ I ^ n, r • h = 0 := by
    intro h
    obtain ⟨z, rfl⟩ := (LinearMap.range b).mkQ_surjective h
    have hgen : ∀ i : s, (i : R) • q z = 0 := by
      intro i
      rw [← q.map_smul]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨(z : s → N) i, ?_⟩
      apply Subtype.ext
      ext j
      exact (hcyc z i j).symm
    intro r hr
    rw [← _hs] at hr
    induction hr using Submodule.span_induction with
    | mem r hr => exact hgen ⟨r, hr⟩
    | zero => simp
    | add r t hr ht ihr iht =>
      change (r + t) • q z = 0
      rw [add_smul, ihr, iht, add_zero]
    | smul t r hr ih =>
      change (t * r) • q z = 0
      rw [mul_smul, ih, smul_zero]
  let E := TensorProduct.piRight R R S (fun _ : s ↦ N)
  let E₂ := TensorProduct.piRight R R S (fun _ : s × s ↦ N)
  have hδ : ∀ t : S ⊗[R] (s → N), ∀ i j : s,
      E₂ (δ.lTensor S t) (i, j) = (i : R) • E t j - (j : R) • E t i := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a z =>
      intro i j
      simp [E, E₂, δ, TensorProduct.tmul_sub, TensorProduct.tmul_smul]
    | add t t' ht ht' =>
      intro i j
      simp only [map_add, Pi.add_apply, ht, ht', smul_add]
      abel
  have hzero : δ.lTensor S (E.symm x) = 0 := by
    apply E₂.injective
    ext ij
    rw [hδ, E.apply_symm_apply]
    simpa using sub_eq_zero.mpr (_hx ij.1 ij.2)
  obtain ⟨t, ht⟩ := (Module.Flat.lTensor_exact S
    (LinearMap.exact_subtype_ker_map δ) (E.symm x)).mp hzero
  have hiso : ∃ e : (R ⧸ I) ≃+* (S ⧸ I.map (algebraMap R S)),
      ∀ r : R, e (Ideal.Quotient.mk I r) =
        Ideal.Quotient.mk (I.map (algebraMap R S)) (algebraMap R S r) := by
    refine ⟨RingEquiv.ofBijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
        Ideal.le_comap_map) hquot, ?_⟩
    intro r
    change Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
      Ideal.le_comap_map (Ideal.Quotient.mk I r) = _
    exact Ideal.quotientMap_mk
  have hT := RingTheory.torsionModule_flat_baseChange_bijective
    (T := H) (algebraMap R S) hflat I hiso
    (fun h ↦ ⟨n, by omega, hkill h⟩)
  have hmodule : Module.compHom S (algebraMap R S) = (inferInstance : Module R S) := by
    ext r a
    exact (Algebra.smul_def r a).symm
  rw [hmodule] at hT
  have hsurj : Function.Surjective (TensorProduct.mk R S H 1) := by
    convert (TensorProduct.comm R H S).surjective.comp hT.2 using 1
    ext h
    simp
  obtain ⟨h, hh⟩ := hsurj (q.lTensor S t)
  obtain ⟨y, hy⟩ := (LinearMap.range b).mkQ_surjective h
  have hqzero : q.lTensor S ((1 : S) ⊗ₜ[R] y - t) = 0 := by
    simp only [map_sub, LinearMap.lTensor_tmul]
    change (1 : S) ⊗ₜ[R] q y - q.lTensor S t = 0
    rw [hy]
    exact sub_eq_zero.mpr hh
  have hex : Function.Exact b q := by
    apply LinearMap.exact_iff.mpr
    exact Submodule.ker_mkQ _
  obtain ⟨m, hm⟩ := (Module.Flat.lTensor_exact S hex
    ((1 : S) ⊗ₜ[R] y - t)).mp hqzero
  have hb : ∀ m : S ⊗[R] N, ∀ i : s,
      E (Z.subtype.lTensor S (b.lTensor S m)) i = (i : R) • m := by
    intro m
    induction m using TensorProduct.inductionOn with
    | tmul a z => intro i; simp [E, b, b₀, TensorProduct.tmul_smul]
    | add m m' hm hm' => intro i; simp [hm, hm', smul_add]
  refine ⟨(y : s → N), m, hcyc y, ?_⟩
  intro i
  have he := congrArg (fun z ↦ E (Z.subtype.lTensor S z) i) hm
  rw [hb] at he
  have hx' : E (Z.subtype.lTensor S t) i = x i := by
    rw [ht, E.apply_symm_apply]
  simp only [map_sub, LinearMap.lTensor_tmul, E, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul, Pi.sub_apply] at he
  change (i : R) • m = (1 : S) ⊗ₜ[R] (y : s → N) i -
    E (Z.subtype.lTensor S t) i at he
  rw [hx'] at he
  exact (sub_eq_iff_eq_add.mp he.symm).trans (add_comm _ _)


/-- A map `d : I^n → S ⊗[R] N` lifts modulo a principal map: there are `l : I^n → N` and
`m ∈ S ⊗[R] N` with `1 ⊗ l r = d r + r • m` for all `r ∈ I^n`. -/
theorem exists_ideal_power_hom_lift
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hflat : (algebraMap R S).Flat) (I : Ideal R) (hI : I.FG)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (n : ℕ) (hn : 1 ≤ n)
    {N : Type w} [AddCommGroup N] [Module R N]
    (d : ↥(I ^ n) →ₗ[R] S ⊗[R] N) :
    ∃ (l : ↥(I ^ n) →ₗ[R] N) (m : S ⊗[R] N),
      ∀ r : ↥(I ^ n), 1 ⊗ₜ[R] l r = d r + (r : R) • m := by
  classical
  obtain ⟨s, hs⟩ := hI.pow (n := n)
  let f : s → ↥(I ^ n) := fun i ↦ ⟨i, hs ▸ Ideal.subset_span i.property⟩
  have hx : ∀ i j : s, (i : R) • d (f j) = (j : R) • d (f i) := by
    intro i j
    rw [← d.map_smul, ← d.map_smul]
    congr 1
    apply Subtype.ext
    exact mul_comm _ _
  obtain ⟨y, m, hy, hym⟩ := exists_finite_koszul_cycle_lift
    hflat I hI hquot n hn s hs (fun i ↦ d (f i)) hx
  let a : (s →₀ R) →ₗ[R] ↥(I ^ n) := Finsupp.linearCombination R f
  let b : (s →₀ R) →ₗ[R] N := Finsupp.linearCombination R y
  let c : N →ₗ[R] S ⊗[R] N := TensorProduct.mk R S N 1
  let p : ↥(I ^ n) →ₗ[R] S ⊗[R] N :=
    (LinearMap.toSpanSingleton R (S ⊗[R] N) m).comp (I ^ n).subtype
  have hbc : c.comp b = (d + p).comp a := by
    ext i
    simpa [a, b, c, p] using hym i
  -- For every relation z, its image b z is killed by J. Applying torsion injectivity
  -- to b z avoids constructing the naive Koszul quotient and its kernel explicitly.
  have hbkill : ∀ z, a z = 0 → ∀ r ∈ I ^ n, r • b z = 0 := by
    intro z hz
    have hgen : ∀ i : s, (i : R) • b z = 0 := by
      intro i
      have he : (i : R) • b z = (a z : R) • y i := by
        simp only [b, a, Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum,
          Finset.sum_smul, Submodule.coe_sum, Submodule.coe_smul, f]
        apply Finset.sum_congr rfl
        intro j hj
        rw [smul_comm (i : R) (z j), hy i j, smul_smul]
        rfl
      rw [he, hz]
      simp
    intro r hr
    rw [← hs] at hr
    induction hr using Submodule.span_induction with
    | mem r hr => exact hgen ⟨r, hr⟩
    | zero => simp
    | add r t hr ht ihr iht => simp [add_smul, ihr, iht]
    | smul t r hr ih => simp [smul_eq_mul, mul_smul, ih]
  have hker : LinearMap.ker a ≤ LinearMap.ker b := by
    intro z hz
    have haz : a z = 0 := hz
    have hbz : b z ∈ Ideal.primaryComponent N I := by
      apply (Ideal.primaryComponent_mem N I (b z)).mpr
      exact ⟨n, (Submodule.mem_torsionBySet_iff _ _).mpr
        (fun r ↦ hbkill z haz r r.property)⟩
    have hc : c (b z) = 0 := by
      have he := congrArg (fun F : (s →₀ R) →ₗ[R] S ⊗[R] N ↦ F z) hbc
      simpa [haz] using he
    have hi := (Ideal.primaryComponent_baseChange_bijective I hI hflat hquot N).1
    have he : Ideal.primaryComponent.map I c ⟨b z, hbz⟩ =
        Ideal.primaryComponent.map I c 0 := by
      apply Subtype.ext
      simpa using hc
    exact congrArg Subtype.val (hi he)
  have ha : Function.Surjective a := by
    intro r
    have hr : (r : R) ∈ Submodule.span R (Set.range (fun i : s ↦ (i : R))) := by
      rw [Subtype.range_coe_subtype]
      change (r : R) ∈ Ideal.span (s : Set R)
      rw [hs]
      exact r.property
    rw [← Finsupp.range_linearCombination, LinearMap.mem_range] at hr
    obtain ⟨z, hz⟩ := hr
    refine ⟨z, Subtype.ext ?_⟩
    simpa [a, f, Finsupp.linearCombination_apply, Finsupp.sum] using hz
  let l : ↥(I ^ n) →ₗ[R] N :=
    ((LinearMap.ker a).liftQ b hker).comp (a.quotKerEquivOfSurjective ha).symm.toLinearMap
  refine ⟨l, m, ?_⟩
  intro r
  obtain ⟨z, rfl⟩ := ha r
  have hl : l (a z) = b z := by simp [l]
  change c (l (a z)) = d (a z) + p (a z)
  rw [hl]
  exact congrArg (fun F : (s →₀ R) →ₗ[R] S ⊗[R] N ↦ F z) hbc

end LinearMap
