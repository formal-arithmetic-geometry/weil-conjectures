/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Data.Finsupp.Fintype

/-! # Detecting invertibility on finite modules

Source: blueprint sk-prop-a1-kummer, Coefficients; the finite free presentation
argument of WeilConjectures.Algebra.Category.ModuleCat.CocontinuousGenerator.
(blueprint: lem-pur-finite-module-generator).
-/

@[expose] public section

universe u v w
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

variable {R : Type u} [CommRing R] {D : Type v} [Category.{w} D]
  {F G : ModuleCat.{u} R ⥤ D}
  [PreservesFiniteColimits F] [PreservesFiniteColimits G] [Finite R]

/-- Finite free presentations detect an isomorphism of right-exact module functors.
Source: blueprint sk-prop-a1-kummer, Coefficients, via the finite free presentation argument.
(blueprint: lem-pur-finite-module-generator).

Proof: extend invertibility from R to finite free modules using finite coproducts.
For a finite module M over the finite ring R, the free module on the elements of M
is finite. Its kernel under the canonical surjection onto M is finite as well.
The free module on that kernel presents M as a cokernel. Both functors preserve
this finite colimit, so invertibility on the two finite free terms implies it on M.
The argument includes the zero ring and the zero module. -/
theorem isIso_app_of_rankOne_of_finite (α : F ⟶ G)
    (h : IsIso (α.app (ModuleCat.of R R))) (M : ModuleCat.{u} R) [Finite M] :
    IsIso (α.app M) := by
  classical
  have hfree (I : Type u) [Finite I] : IsIso (α.app ((free R).obj I)) := by
    let c : Cofan (fun _ : I ↦ ModuleCat.of R R) :=
      Cofan.mk ((free R).obj I) (fun i ↦ ModuleCat.ofHom
        ((LinearMap.ringLmapEquivSelf R ℤ ((free R).obj I)).symm (freeMk i)))
    have hc : IsColimit c := by
      refine Cofan.IsColimit.mk _
        (fun s ↦ freeDesc (↾fun i ↦ s.inj i 1)) ?_ ?_
      · intro s i
        apply ModuleCat.hom_ext
        apply LinearMap.ext_ring
        simp [c]
      · intro s m hm
        apply free_hom_ext
        intro i
        have hi := congrArg (fun f : ModuleCat.of R R ⟶ s.pt ↦ f 1) (hm i)
        simpa [c, ModuleCat.comp_apply] using hi
    let K := Discrete.functor (fun _ : I ↦ ModuleCat.of R R)
    have : ∀ j, IsIso ((Functor.whiskerLeft K α).app j) := fun _ ↦ h
    have : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit K α c hc
  let : Fintype R := Fintype.ofFinite R
  let : Fintype M := Fintype.ofFinite M
  have : Finite ((free R).obj M) := by
    change Finite (M →₀ R)
    infer_instance
  let g : (free R).obj M ⟶ M := freeDesc (↾fun m ↦ m)
  let f : (free R).obj g.hom.ker ⟶ (free R).obj M := freeDesc (↾fun x ↦ x.val)
  have hg : Function.Surjective g.hom := by
    intro m
    exact ⟨freeMk m, freeDesc_apply _ _⟩
  have hfg : Function.Exact f.hom g.hom := by
    intro x
    constructor
    · intro hx
      exact ⟨freeMk (⟨x, hx⟩ : g.hom.ker), freeDesc_apply _ _⟩
    · rintro ⟨y, rfl⟩
      have heq : g.hom.comp f.hom = 0 := by
        apply Finsupp.lhom_ext'
        intro y
        apply LinearMap.ext_ring
        change g (f (freeMk y)) = 0
        rw [show f (freeMk y) = y.val from freeDesc_apply _ _]
        exact y.property
      exact LinearMap.congr_fun heq y
  let K := parallelPair f 0
  have : ∀ j, IsIso ((Functor.whiskerLeft K α).app j) := by
    intro j
    cases j <;> apply hfree
  have : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit K α _
    (ModuleCat.isColimitCokernelCofork f g hfg hg)

end ModuleCat
