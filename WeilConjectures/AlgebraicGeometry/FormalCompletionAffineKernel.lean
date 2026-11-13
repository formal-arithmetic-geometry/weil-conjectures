/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.FormalCompletionAffineComparison
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The affine kernel fork of a completed short exact sequence

## References

* Stacks Project, Tags 0881, 087W, 087X and 00MB
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- On an affine open, the completed first arrow is a kernel of the completed second
arrow. The restriction functor is specified by its equality after the full inclusion;
no arbitrary replacement of the restriction functor is allowed. The conclusion asserts
only the kernel universal property, not that the completed second arrow is epimorphic
(Stacks, Tag 0881; Tag 087W). -/
theorem formalCompletion_affine_kernel (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) (h : (completion X I).Additive)
    (U : X.Opens) [IsNoetherian U.toScheme] (hU : IsAffineOpen U)
    (ρ : CoherentFormalModule X I ⥤ CoherentFormalModule U.toScheme (I.comap U.ι))
    (hz : ρ.PreservesZeroMorphisms)
    (hρ : ρ ⋙ (IsCoherentFormalModule (I.comap U.ι)).ι =
      (IsCoherentFormalModule I).ι ⋙
        (Functor.whiskeringRight ℕᵒᵖ X.Modules U.toScheme.Modules).obj
          (Scheme.Modules.restrictFunctor U.ι))
    (S : ShortComplex (CoherentModules X)) (hS : S.ShortExact) :
    let T := @ShortComplex.map _ _ _ _ _ _ S (completion X I)
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ (completion X I) h)
    let V := @ShortComplex.map _ _ _ _ _ _ T ρ hz
    Nonempty (IsLimit (KernelFork.ofι V.f V.zero)) := by
  classical
  let T := @ShortComplex.map _ _ _ _ _ _ S (completion X I)
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ (completion X I) h)
  let V := @ShortComplex.map _ _ _ _ _ _ T ρ hz
  obtain ⟨A, hA, hN, J, M, hfinite, hM, F, hFzero, hFreflect,
      e₁, e₂, e₃, hf, hg⟩ := formalCompletion_affine_comparison X I h U hU ρ hz hρ S hS
  have : Module.Finite A M.X₂ := hfinite
  have : F.PreservesZeroMorphisms := hFzero
  have : ReflectsLimitsOfShape WalkingParallelPair F := hFreflect
  let W := @ShortComplex.map _ _ _ _ _ _ V F hFzero
  have hf : ∀ x : W.X₁, e₂ (W.f x) = AdicCompletion.map J M.f.hom (e₁ x) := hf
  have hg : ∀ x : W.X₂, e₃ (W.g x) = AdicCompletion.map J M.g.hom (e₂ x) := hg
  have hfinj := AdicCompletion.map_injective J hM.moduleCat_injective_f
  have hexact := AdicCompletion.map_exact hM.moduleCat_injective_f
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact M).mp hM.exact)
    hM.moduleCat_surjective_g (I := J)
  have hinj : Function.Injective W.f := by
    intro x y hxy
    apply e₁.injective
    apply hfinj
    rw [← hf x, ← hf y, hxy]
  have he : Function.Exact W.f W.g := by
    intro y
    constructor
    · intro hy
      have hy' : AdicCompletion.map J M.g.hom (e₂ y) = 0 := by
        rw [← hg y, hy, map_zero]
      obtain ⟨x, hx⟩ := (hexact (e₂ y)).mp hy'
      refine ⟨e₁.symm x, ?_⟩
      apply e₂.injective
      rw [hf, e₁.apply_symm_apply, hx]
    · rintro ⟨x, rfl⟩
      exact W.moduleCat_zero_apply x
  have : Mono W.f := (ModuleCat.mono_iff_injective W.f).mpr hinj
  have hW : W.Exact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact W).mpr he
  exact ⟨isLimitOfReflects F
    (((KernelFork.ofι V.f V.zero).isLimitMapConeEquiv F).symm hW.fIsKernel)⟩

end AlgebraicGeometry
