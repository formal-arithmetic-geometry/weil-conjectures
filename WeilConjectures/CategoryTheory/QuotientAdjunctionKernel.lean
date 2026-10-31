/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # The coinduction counit is the scalar kernel

Source: The unit/counit hom-set formulas for an adjoint triple; Stacks Tag 03D7, scalar
restriction and its adjoints.
(blueprint: lem-sf-quotient-adjunction-kernel). -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- If the unit of extension is a scalar cokernel and the scalar vanishes on
restricted objects, the counit of coinduction is the corresponding scalar kernel.
Source: The unit/counit hom-set formulas for an adjoint triple; Stacks Tag 03D7, scalar
restriction and its adjoints.
(blueprint: lem-sf-quotient-adjunction-kernel). -/
theorem quotientAdjunctionKernel
    {A B : Type*} [Category* A] [Category* B] [HasZeroMorphisms A]
    {E : A ⥤ B} {U : B ⥤ A} {C : A ⥤ B} (a : E ⊣ U) (b : U ⊣ C)
    (α : 𝟭 A ⟶ 𝟭 A) (hU : ∀ N : B, α.app (U.obj N) = 0)
    (hz : ∀ M : A, α.app M ≫ a.unit.app M = 0)
    (hquot : ∀ M : A, IsColimit (CokernelCofork.ofπ (a.unit.app M) (hz M)))
    (I : A) :
    ∃ h : b.counit.app I ≫ α.app I = 0,
      Nonempty (IsLimit (KernelFork.ofι (b.counit.app I) h)) := by
  have hzero : b.counit.app I ≫ α.app I = 0 := by
    simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj, hU, zero_comp] using
      α.naturality (b.counit.app I)
  refine ⟨hzero, ⟨?_⟩⟩
  let k {M : A} (g : M ⟶ I) (hg : g ≫ α.app I = 0) : U.obj (E.obj M) ⟶ I :=
    (hquot M).desc (CokernelCofork.ofπ g (by
      simpa only [Functor.id_map, hg] using (α.naturality g).symm))
  have hk {M : A} (g : M ⟶ I) (hg : g ≫ α.app I = 0) :
      a.unit.app M ≫ k g hg = g :=
    (hquot M).fac (CokernelCofork.ofπ g (by
      simpa only [Functor.id_map, hg] using (α.naturality g).symm))
      WalkingParallelPair.one
  let lift {M : A} (g : M ⟶ I) (hg : g ≫ α.app I = 0) : M ⟶ U.obj (C.obj I) :=
    a.homEquiv _ _ (b.homEquiv _ _ (k g hg))
  refine KernelFork.IsLimit.ofι _ _ (fun g hg ↦ lift g hg) ?_ ?_
  · intro M g hg
    change a.homEquiv _ _ (b.homEquiv _ _ (k g hg)) ≫ b.counit.app I = g
    rw [Adjunction.homEquiv_unit, Category.assoc]
    have h := (b.homEquiv _ _).symm_apply_apply (k g hg)
    change U.map (b.homEquiv _ _ (k g hg)) ≫ b.counit.app I = k g hg at h
    exact (congrArg (fun z ↦ a.unit.app M ≫ z) h).trans (hk g hg)
  · intro M g hg m hm
    apply (a.homEquiv _ _).symm.injective
    simp only [lift, Equiv.symm_apply_apply]
    apply (b.homEquiv _ _).symm.injective
    simp only [Equiv.symm_apply_apply]
    have : Epi (a.unit.app M) := epi_of_isColimit_cofork (hquot M)
    apply (cancel_epi (a.unit.app M)).mp
    rw [hk g hg, Adjunction.homEquiv_counit, ← Category.assoc]
    have he : a.unit.app M ≫ U.map ((a.homEquiv _ _).symm m) = m := by
      simpa only [Adjunction.homEquiv_unit] using (a.homEquiv _ _).apply_symm_apply m
    exact (congrArg (fun z ↦ z ≫ b.counit.app I) he).trans hm

end CategoryTheory
