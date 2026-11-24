/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Ideal.Defs

/-!
# Kernels, images, and cokernels of finitely presented modules over a coherent ring

Over a commutative ring whose finitely generated ideals are finitely presented, finitely
generated submodules of finitely presented modules are finitely presented; hence kernels,
images and cokernels of maps between finitely presented modules are finitely presented.

## Main results

- `Module.finitePresentation_ker_range_cokernel_of_fg_ideals`

## References

- Stacks Project, Algebra, Definition 05CU and Lemmas 05CW, 05CX.
-/

@[expose] public section

universe u v w

namespace Module

private theorem fp_submodule_equiv
    {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N)
    (hN : ∀ S : Submodule R N, S.FG → FinitePresentation R S)
    (S : Submodule R M) (hS : S.FG) : FinitePresentation R S := by
  have := hN (S.map e.toLinearMap) (hS.map e.toLinearMap)
  exact FinitePresentation.of_equiv (S.equivMapOfInjective e.toLinearMap e.injective).symm

private theorem fp_submodule_prod
    {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hM : ∀ S : Submodule R M, S.FG → FinitePresentation R S)
    (hN : ∀ S : Submodule R N, S.FG → FinitePresentation R S)
    (S : Submodule R (M × N)) (hS : S.FG) : FinitePresentation R S := by
  -- Project to the first factor; its finitely presented image gives a finite kernel.
  let p : S →ₗ[R] M := (LinearMap.fst R M N).comp S.subtype
  have hp : FinitePresentation R (LinearMap.range p) :=
    hM _ (by simpa [p, LinearMap.range_comp] using hS.map (LinearMap.fst R M N))
  have : Module.Finite R S := .of_fg hS
  have hK := FinitePresentation.fg_ker p.rangeRestrict p.surjective_rangeRestrict
  -- On that kernel the second projection is injective.
  let q : LinearMap.ker p.rangeRestrict →ₗ[R] N :=
    (LinearMap.snd R M N).comp (S.subtype.comp (LinearMap.ker p.rangeRestrict).subtype)
  have hq : Function.Injective q := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have hx : (x.val.val).1 = 0 := congrArg Subtype.val x.property
      have hy : (y.val.val).1 = 0 := congrArg Subtype.val y.property
      exact hx.trans hy.symm
    · exact h
  have hKfinite : Module.Finite R (LinearMap.ker p.rangeRestrict) := .of_fg hK
  have : FinitePresentation R (LinearMap.range q) := hN _ (Submodule.fg_range q)
  have : FinitePresentation R (LinearMap.ker p.rangeRestrict) :=
    FinitePresentation.of_equiv (LinearEquiv.ofInjective q hq).symm
  exact finitePresentation_of_ker p.rangeRestrict p.surjective_rangeRestrict

private theorem fp_submodule_fin
    {R : Type u} [CommRing R]
    (hR : ∀ (I : Ideal R), I.FG → FinitePresentation R I)
    (n : ℕ) (S : Submodule R (Fin n → R)) (hS : S.FG) :
    FinitePresentation R S := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
    let e := LinearEquiv.piCongrLeft R (fun _ ↦ R) (finSuccEquiv n) ≪≫ₗ
      LinearEquiv.piOptionEquivProd R
    exact fp_submodule_equiv e (fp_submodule_prod hR ih) S hS

private theorem fp_fg_submodule
    {R : Type u} [CommRing R]
    (hR : ∀ (I : Ideal R), I.FG → FinitePresentation R I)
    {M : Type v} [AddCommGroup M] [Module R M] [FinitePresentation R M]
    (S : Submodule R M) (hS : S.FG) : FinitePresentation R S := by
  -- Pull S back to a finite free presentation, then descend along its finite kernel.
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  have hker := FinitePresentation.fg_ker p hp
  let T := S.comap p
  have hT : T.FG := by
    apply Submodule.fg_of_fg_map_of_fg_inf_ker p
    · simpa [T, Submodule.map_comap_eq_of_surjective hp] using hS
    · simpa [T, inf_eq_right.mpr (show LinearMap.ker p ≤ S.comap p from
        fun x hx ↦ by simpa only [Submodule.mem_comap, LinearMap.mem_ker.mp hx]
          using S.zero_mem)] using hker
  have : FinitePresentation R T := fp_submodule_fin hR n T hT
  let q : T →ₗ[R] S := p.restrict (fun x ↦ id)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨y, hy⟩ := hp x.val
    exact ⟨⟨y, by change p y ∈ S; rw [hy]; exact x.property⟩, Subtype.ext hy⟩
  apply finitePresentation_of_surjective q hq
  have heq : (LinearMap.ker q).map T.subtype = LinearMap.ker p := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact congrArg Subtype.val hy
    · intro hx
      refine ⟨⟨x, ?_⟩, ?_, rfl⟩
      · change p x ∈ S
        rw [LinearMap.mem_ker.mp hx]
        exact S.zero_mem
      · apply Subtype.ext
        exact hx
  rw [← Submodule.fg_map_iff T.subtype T.injective_subtype, heq]
  exact hker

/-- Over a commutative ring whose finitely generated ideals are finitely presented, kernels,
images, and cokernels of maps between finitely presented modules are finitely presented. -/
theorem finitePresentation_ker_range_cokernel_of_fg_ideals
    {R : Type u} [CommRing R]
    (hR : ∀ (I : Ideal R), I.FG → Module.FinitePresentation R I)
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (f : M →ₗ[R] N) :
    Module.FinitePresentation R (LinearMap.ker f) ∧
      Module.FinitePresentation R (LinearMap.range f) ∧
      Module.FinitePresentation R (N ⧸ LinearMap.range f) := by
  have hI : FinitePresentation R (LinearMap.range f) :=
    fp_fg_submodule hR _ (Submodule.fg_range f)
  have hK : (LinearMap.ker f).FG := by
    simpa using FinitePresentation.fg_ker f.rangeRestrict f.surjective_rangeRestrict
  refine ⟨fp_fg_submodule hR _ hK, hI, ?_⟩
  exact finitePresentation_of_surjective (LinearMap.range f).mkQ
    (LinearMap.range f).mkQ_surjective
    (by simpa only [Submodule.ker_mkQ] using Submodule.fg_range f)

end Module
