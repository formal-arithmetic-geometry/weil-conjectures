/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Order.RelClasses
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Abelian

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.RingTheory.WellOrderedPresentationComponentData

/-!
# Partial sums and kernel projections for a well-ordered presentation

## Implementation details

The presentation is the direct sum, over the active indices (those with nonzero successive
quotient), of the degree-zero terms of the supplied resolutions. The active indices inject into
`M`, so the construction stays in universe `v` and needs no size assumption on `R`. The kernel
stages are the pullbacks of the partial sums along the kernel inclusion.

## References

* [Stacks Project, Lemma 0D1U](https://stacks.math.columbia.edu/tag/0D1U), successor argument,
  with the supplied projective presentations in place of free modules
-/

@[expose] public section

universe u v w

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits

private theorem predecessor_comap
    {R : Type u} [CommRing R] {A B : Type v}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    {E : Type w} [LinearOrder E] (H : E → Submodule R B) (hH : Monotone H)
    (f : A →ₗ[R] B) (hf : Function.Injective f) (e : E) :
    (⨆ i : {j : E // j < e}, H i.val).comap f =
      ⨆ i : {j : E // j < e}, (H i.val).comap f := by
  classical
  by_cases hn : Nonempty {j : E // j < e}
  · have := hn
    have hm : Monotone (fun i : {j : E // j < e} ↦ H i.val) :=
      fun _ _ h ↦ hH h
    have hd := hm.directed_le
    have hmc : Monotone (fun i : {j : E // j < e} ↦ (H i.val).comap f) :=
      fun _ _ h ↦ Submodule.comap_mono (hm h)
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_iSup_of_directed _ hd,
      Submodule.mem_iSup_of_directed _ hmc.directed_le]
  · have : IsEmpty {j : E // j < e} := not_nonempty_iff.mp hn
    simp only [iSup_of_empty, Submodule.comap_bot, LinearMap.ker_eq_bot.mpr hf]

/-- A short exact projective presentation `0 → K → P → M → 0` with an exhaustive monotone
filtration of `P` such that each induced stage of `K` either adds nothing to the earlier stages
or surjects onto the corresponding augmentation kernel with kernel the earlier stages. -/
theorem exists_projective_presentation_kernel_projection_data
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    {E : Type w} [LinearOrder E] [IsWellOrder E (· < ·)]
    (F : E → Submodule R M) (hF : Monotone F)
    (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
    (P : ∀ e : E, ProjectiveResolution
      (ModuleCat.of R ((F e) ⧸
        ((⨆ i : {j : E // j < e}, F i.val).comap (F e).subtype)))) :
    ∃ S : ShortComplex (ModuleCat.{v} R), S.X₃ = M ∧ S.ShortExact ∧
      Projective S.X₂ ∧ ∃ H : E → Submodule R S.X₂,
        Monotone H ∧ (∀ x : S.X₂, ∃ e : E, x ∈ H e) ∧
        ∀ e : E,
          let K : E → Submodule R S.X₁ := fun i ↦ (H i).comap S.f.hom
          let U := (⨆ i : {j : E // j < e}, K i.val).comap (K e).subtype
          U = ⊤ ∨ ∃ q : K e →ₗ[R] (kernel ((P e).π.f 0) : ModuleCat.{v} R),
            Function.Surjective q ∧ q.ker = U := by
  classical
  obtain ⟨B, hB, b, H, hH, hHcover, himage, hpieces⟩ :=
    exists_projective_presentation_component_data M F hF hcover P
  have hb : Function.Surjective b := by
    intro x
    obtain ⟨e, he⟩ := hcover x
    rw [← himage e] at he
    obtain ⟨y, hy, rfl⟩ := he
    exact ⟨y, rfl⟩
  let S : ShortComplex (ModuleCat.{v} R) := b.shortComplexKer
  refine ⟨S, rfl, b.shortExact_shortComplexKer hb, hB, H, hH, hHcover, ?_⟩
  intro e
  let V : Submodule R B := ⨆ i : {j : E // j < e}, H i.val
  let K : E → Submodule R b.ker := fun i ↦ (H i).comap b.ker.subtype
  have hpred : V.comap b.ker.subtype = ⨆ i : {j : E // j < e}, K i.val :=
    predecessor_comap H hH b.ker.subtype b.ker.injective_subtype e
  change (⨆ i : {j : E // j < e}, K i.val).comap (K e).subtype = ⊤ ∨ _
  rcases hpieces e with hinactive | ⟨p, hp, hpker, a, ha, hcomm⟩
  · left
    change H e = V at hinactive
    rw [← hpred, ← hinactive]
    exact Submodule.comap_subtype_self (K e)
  · right
    let j : K e →ₗ[R] H e :=
      (b.ker.subtype.comp (K e).subtype).codRestrict (H e) (fun x ↦ x.property)
    have haj : ∀ x : K e, a (j x) = 0 := by
      intro x
      apply Subtype.ext
      change (F e).subtype (a (j x)) = 0
      have hax : (a (j x)).val = b x.val.val := LinearMap.congr_fun ha (j x)
      exact hax.trans x.val.property
    have hqzero : ∀ x : K e, ((P e).π.f 0).hom (p (j x)) = 0 := by
      intro x
      have hc : ((P e).π.f 0).hom (p (j x)) =
          ((⨆ i : {j : E // j < e}, F i.val).comap (F e).subtype).mkQ (a (j x)) :=
        LinearMap.congr_fun hcomm (j x)
      rw [haj, map_zero] at hc
      exact hc
    let qlin : K e →ₗ[R] ((P e).π.f 0).hom.ker :=
      (p.comp j).codRestrict _ hqzero
    have hVle : V ≤ H e := iSup_le (fun i ↦ hH (le_of_lt i.property))
    have hVmap : V.map b = ⨆ i : {j : E // j < e}, F i.val := by
      simp only [V, Submodule.map_iSup, himage]
    have hsurj : Function.Surjective qlin := by
      intro y
      obtain ⟨x, hx⟩ := hp y.val
      have hazero :
          ((⨆ i : {j : E // j < e}, F i.val).comap (F e).subtype).mkQ (a x) = 0 := by
        calc
          _ = ((P e).π.f 0).hom (p x) := (LinearMap.congr_fun hcomm x).symm
          _ = 0 := by rw [hx]; exact y.property
      have hamem := (Submodule.Quotient.mk_eq_zero _).mp hazero
      have hbx : b x.val ∈ ⨆ i : {j : E // j < e}, F i.val := by
        have hax := LinearMap.congr_fun ha x
        change (a x).val = b x.val at hax
        change (a x).val ∈ (⨆ i : {j : E // j < e}, F i.val) at hamem
        rwa [← hax]
      rw [← hVmap] at hbx
      obtain ⟨z, hz, hzx⟩ := hbx
      let z' : H e := ⟨z, hVle hz⟩
      have hpz : p z' = 0 := by
        apply LinearMap.mem_ker.mp
        rw [hpker]
        exact hz
      have hbt : b (x.val - z) = 0 := by
        rw [map_sub, hzx, sub_self]
      let t : K e := ⟨⟨x.val - z, hbt⟩, (H e).sub_mem x.property (hVle hz)⟩
      refine ⟨t, ?_⟩
      apply Subtype.ext
      change p (j t) = y.val
      have hjt : j t = x - z' := rfl
      rw [hjt, map_sub, hpz, sub_zero, hx]
    have hker : qlin.ker =
        (⨆ i : {j : E // j < e}, K i.val).comap (K e).subtype := by
      rw [← hpred]
      ext x
      change qlin x = 0 ↔ x.val.val ∈ V
      rw [Subtype.ext_iff]
      change p (j x) = 0 ↔ x.val.val ∈ V
      rw [← LinearMap.mem_ker, hpker]
      rfl
    let equiv := (ModuleCat.kernelIsoKer ((P e).π.f 0)).symm.toLinearEquiv
    refine ⟨equiv.toLinearMap.comp qlin, equiv.surjective.comp hsurj, ?_⟩
    rw [LinearEquiv.ker_comp, hker]
    rfl

end ModuleCat
