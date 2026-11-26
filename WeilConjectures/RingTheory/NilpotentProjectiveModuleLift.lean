/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Idempotents

/-!
# Lifting projective modules across nilpotent quotients

A projective module over `A / I`, with `I` a nilpotent ideal, lifts to a projective `A`-module.

## Implementation details

Realize `Pbar` as the image of an idempotent `pbar` on a free module `(A / I)^(S)`, lift it to an
endomorphism `p` of `F = A^(S)`, and note that `x = p² - p` is nilpotent. Lifting the idempotent
of `ℤ[t] / ((t² - t)^N)` and evaluating at `p` gives an idempotent `e` lifting `pbar`
(the polynomial correction of Stacks, Tag 05BU); then `P = im e`.

## References

* [Stacks, Tag 07LV]
* [Stacks, Tag 00J9]
* [Stacks, Tag 05BU]
-/

@[expose] public section

universe u v

open scoped Pointwise

namespace Module

private def reductionEnd (A : Type u) [CommRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] :
    Module.End A M →+* Module.End A (M ⧸ I • (⊤ : Submodule A M)) where
  toFun f := (I • (⊤ : Submodule A M)).mapQ _ f
    (Submodule.smul_top_le_comap_smul_top I f)
  map_one' := by
    ext x
    rfl
  map_mul' f g := by
    ext x
    rfl
  map_zero' := by
    ext x
    rfl
  map_add' f g := by
    ext x
    rfl

private theorem reductionEnd_ker_nilpotent (A : Type u) [CommRing A] (I : Ideal A)
    (N : ℕ) (hI : I ^ N = ⊥) (M : Type v) [AddCommGroup M] [Module A M]
    (f : Module.End A M) (hf : f ∈ RingHom.ker (reductionEnd A I M)) :
    IsNilpotent f := by
  have hr : LinearMap.range f ≤ I • (⊤ : Submodule A M) := by
    rintro _ ⟨x, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact DFunLike.congr_fun (RingHom.mem_ker.mp hf) (Submodule.Quotient.mk x)
  have hp (n : ℕ) : LinearMap.range (f ^ n) ≤ I ^ n • (⊤ : Submodule A M) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]
      calc
        (LinearMap.range (f ^ n)).map f ≤ (I ^ n • (⊤ : Submodule A M)).map f :=
          Submodule.map_mono ih
        _ = I ^ n • LinearMap.range f := by rw [Submodule.map_smul'', Submodule.map_top]
        _ ≤ I ^ n • (I • (⊤ : Submodule A M)) := smul_mono_right _ hr
        _ = I ^ (n + 1) • (⊤ : Submodule A M) := by
          rw [pow_succ, Submodule.mul_smul]
  refine ⟨N, ?_⟩
  apply LinearMap.ext
  intro x
  have hx := hp N (LinearMap.mem_range_self (f ^ N) x)
  simpa [hI] using hx

/-- A projective module over `A / I`, with `I` nilpotent, lifts to a projective `A`-module `P`
with `P / I P ≃ Pbar`, without any finite generation assumption. -/
theorem exists_projective_lift_of_nilpotent_ideal
    (A : Type u) [CommRing A] (I : Ideal A) (N : ℕ) (hN : 1 ≤ N)
    (hI : I ^ N = ⊥) (Pbar : Type v) [AddCommGroup Pbar] [Module (A ⧸ I) Pbar]
    [Module.Projective (A ⧸ I) Pbar] :
    ∃ P : ModuleCat.{max u v} A, Module.Projective A P ∧
      Nonempty ((P ⧸ (I • (⊤ : Submodule A P))) ≃ₗ[A ⧸ I] Pbar) := by
  classical
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  let : Module A Pbar := Module.compHom Pbar (Ideal.Quotient.mk I)
  let : IsScalarTower A (A ⧸ I) Pbar := IsScalarTower.of_compHom A (A ⧸ I) Pbar
  let F := Pbar →₀ A
  let K : Submodule A F := I • ⊤
  let Q := F ⧸ K
  let r : F →ₗ[A] Pbar := Finsupp.linearCombination A id
  have hr : Function.Surjective r := by
    intro x
    refine ⟨Finsupp.single x 1, ?_⟩
    exact (Finsupp.linearCombination_single A (v := id) 1 x).trans (one_smul A x)
  have hKr : K ≤ LinearMap.ker r := by
    apply Submodule.smul_le.mpr
    intro a ha x _
    rw [LinearMap.mem_ker, r.map_smul]
    change Ideal.Quotient.mk I a • r x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_smul]
  let rQ : Q →ₗ[A] Pbar := K.liftQ r hKr
  let s : Q →ₗ[A ⧸ I] Pbar :=
    { toFun := rQ
      map_add' := rQ.map_add
      map_smul' := by
        intro a x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact rQ.map_smul a x }
  have hs : Function.Surjective s := by
    intro x
    obtain ⟨y, hy⟩ := hr x
    exact ⟨K.mkQ y, hy⟩
  obtain ⟨i', hi'⟩ := Module.projective_lifting_property s LinearMap.id hs
  let i : Pbar →ₗ[A] Q := i'.restrictScalars A
  have hsi (x : Pbar) : rQ (i x) = x := DFunLike.congr_fun hi' x
  let pbar : Module.End A Q := i.comp rQ
  have hpbar : IsIdempotentElem pbar := by
    apply LinearMap.ext
    intro x
    exact congrArg i (hsi (rQ x))
  obtain ⟨p, hp⟩ := Module.projective_lifting_property K.mkQ (pbar.comp K.mkQ)
    K.mkQ_surjective
  have hpr : pbar ∈ (reductionEnd A I F).range := by
    refine ⟨p, ?_⟩
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := K.mkQ_surjective x
    exact DFunLike.congr_fun hp x
  obtain ⟨e, he, hebar⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (reductionEnd A I F) (reductionEnd_ker_nilpotent A I (N + 1) hI F) pbar hpr hpbar
  have heq (x : F) : K.mkQ (e x) = i (r x) :=
    DFunLike.congr_fun hebar (K.mkQ x)
  let P := LinearMap.range e
  let t : F →ₗ[A] P := e.rangeRestrict
  have het (x : P) : e x = x := by
    obtain ⟨y, hy⟩ := x.property
    rw [← hy]
    exact DFunLike.congr_fun he.eq y
  have hsplit : t.comp P.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact het x
  have hproj : Module.Projective A P := Module.Projective.of_split P.subtype t hsplit
  let f : P →ₗ[A] Pbar := r.comp P.subtype
  have hfs : Function.Surjective f := by
    intro x
    obtain ⟨y, hy⟩ := K.mkQ_surjective (i x)
    refine ⟨t y, ?_⟩
    change r (e y) = x
    have h := congrArg rQ (heq y)
    change r (e y) = rQ (i (r y)) at h
    rw [hsi] at h
    rw [h]
    have hx := congrArg rQ hy
    exact hx.trans (hsi x)
  have hker : LinearMap.ker f = I • (⊤ : Submodule A P) := by
    apply le_antisymm
    · intro x hx
      have hx0 : r x = 0 := hx
      have hxK : (x : F) ∈ K := by
        apply (Submodule.Quotient.mk_eq_zero _).mp
        have hxq := heq x
        rw [het x, hx0, map_zero] at hxq
        exact hxq
      have hxt := Submodule.smul_top_le_comap_smul_top I t hxK
      change t x ∈ I • (⊤ : Submodule A P) at hxt
      have htx : t x = x := by
        apply Subtype.ext
        exact het x
      rwa [htx] at hxt
    · apply Submodule.smul_le.mpr
      intro a ha x _
      rw [LinearMap.mem_ker, f.map_smul]
      change Ideal.Quotient.mk I a • f x = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_smul]
  let J : Submodule A P := I • ⊤
  let g : (P ⧸ J) →ₗ[A] Pbar := J.liftQ f hker.ge
  have hgi : Function.Injective g := by
    apply LinearMap.ker_eq_bot.mp
    exact J.ker_liftQ_eq_bot f hker.ge hker.le
  have hgs : Function.Surjective g := by
    intro x
    obtain ⟨y, hy⟩ := hfs x
    exact ⟨J.mkQ y, hy⟩
  let g' : (P ⧸ J) →ₗ[A ⧸ I] Pbar :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        intro a x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact g.map_smul a x }
  exact ⟨ModuleCat.of A P, hproj, ⟨LinearEquiv.ofBijective g' ⟨hgi, hgs⟩⟩⟩

end Module
