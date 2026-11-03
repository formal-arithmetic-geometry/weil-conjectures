/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralOrdinaryQuotientKernelLift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralOrdinaryQuotientKernelSeparated

/-! # Completeness kernel for ordinary positive quotients

Source: Hemo--Richarz--Scholbach, Propositions 5.1 and 7.6 and Theorem 7.7;
Bhatt--Scholze, Section 6.1.
(blueprint: lem-sp-original-integral-ordinary-quotient-kernel)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry Scheme

/-- The ordinary positive quotient augmentation is the kernel of one minus the shift.

Source: Hemo--Richarz--Scholbach, Propositions 5.1 and 7.6 and Theorem 7.7;
Bhatt--Scholze, Section 6.1.
(blueprint: lem-sp-original-integral-ordinary-quotient-kernel).

Proof: on every extremally disconnected w-contractible affine test of a constructible
stratum, a finite presentation has a compact space of integral solutions. Projectivity
of the component space lifts compatible solutions through all ordinary positive
quotients, proving separatedness and completeness. Exact open and closed localization
reassembles the finite stratification, and repleteness identifies the resulting inverse
limit with the kernel of one minus the quotient shift. The assertion is then checked
on the internal module sections and transported across the section equivalence. -/
theorem originalIntegralOrdinaryQuotientKernel
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (X : Scheme.{u})
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X) M) :
    Nonempty (IsLimit (KernelFork.ofι
      (CategoryTheory.OriginalIntegralQuotientSequence.augmentation ell M)
      (CategoryTheory.OriginalIntegralQuotientSequence.augmentation_comp_one_sub ell M))) := by
  classical
  let a := CategoryTheory.OriginalIntegralQuotientSequence.augmentation ell M
  let t := CategoryTheory.OriginalIntegralQuotientSequence.shift ell M
  have hzero : a ≫ (𝟙 _ - t) = 0 :=
    CategoryTheory.OriginalIntegralQuotientSequence.augmentation_comp_one_sub ell M
  let glift {W : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X)}
      (k : W ⟶ _) (hk : k ≫ (𝟙 _ - t) = 0) : W ⟶ M :=
    Classical.choose (originalIntegralOrdinaryQuotientKernel_lift ell E X M hM k hk)
  have glift_spec {W : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X)}
      (k : W ⟶ _) (hk : k ≫ (𝟙 _ - t) = 0) :
      glift k hk ≫ a = k :=
    Classical.choose_spec (originalIntegralOrdinaryQuotientKernel_lift ell E X M hM k hk)
  refine ⟨KernelFork.IsLimit.ofι a hzero (fun {W} k hk ↦ glift k hk) ?_ ?_⟩
  · intro W k hk
    exact glift_spec k hk
  · intro W k hk m hm
    have hd : (m - glift k hk) ≫ a = 0 := by
      rw [Preadditive.sub_comp, hm, glift_spec k hk, sub_self]
    have hz := originalIntegralOrdinaryQuotientKernel_separated ell E X M hM
      (m - glift k hk) hd
    exact sub_eq_zero.mp hz

end AlgebraicGeometry.ProEtale.CondensedRing
