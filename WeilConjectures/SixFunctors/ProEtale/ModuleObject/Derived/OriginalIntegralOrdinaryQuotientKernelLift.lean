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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralOrdinaryQuotientFiniteLifts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralOrdinaryQuotientCompatibleLimit

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry Scheme

private theorem quotientAgreement_down
    {A : Type*} [Category A] {M W : A}
    (Q : ℕ → A) (q : ∀ n, M ⟶ Q n) (t : ∀ n, Q (n + 1) ⟶ Q n)
    (hq : ∀ n, q (n + 1) ≫ t n = q n)
    (n m : ℕ) (hnm : n ≤ m) (f g : W ⟶ M)
    (hfg : f ≫ q m = g ≫ q m) : f ≫ q n = g ≫ q n := by
  induction m, hnm using Nat.le_induction with
  | base => exact hfg
  | succ m hnm ih =>
    apply ih
    calc
      f ≫ q m = (f ≫ q (m + 1)) ≫ t m := by rw [Category.assoc, hq]
      _ = (g ≫ q (m + 1)) ≫ t m := by rw [hfg]
      _ = g ≫ q m := by rw [Category.assoc, hq]

/-- Compatible families of ordinary quotient maps lift to the integral module.

Source: Hemo--Richarz--Scholbach, Propositions 5.1 and 7.6 and Theorem 7.7;
Bhatt--Scholze, Section 6.1.
(blueprint: lem-sp-original-integral-ordinary-quotient-kernel-lift).

The finite-presentation reconstruction on each extremally disconnected
w-contractible affine test produces compatible integral lifts of a family of
ordinary quotient sections. Compactness and projectivity give continuity of the
lift, and exact open/closed localization reassembles the local lifts. -/
theorem originalIntegralOrdinaryQuotientKernel_lift
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (X : Scheme.{u})
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X) M)
    {W : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X)}
    (k : W ⟶ ∏ᶜ (fun n : ℕ ↦ cokernel (ell ^ (n + 1) • 𝟙 M)))
    (hk : k ≫ (𝟙 _ - CategoryTheory.OriginalIntegralQuotientSequence.shift ell M) = 0) :
    ∃ g : W ⟶ M, g ≫ CategoryTheory.OriginalIntegralQuotientSequence.augmentation ell M = k := by
  classical
  choose a ha using originalIntegralOrdinaryQuotient_finiteLifts ell E X M hM k hk
  have hcompat (n : ℕ) :
      (a (n + 1) - a n) ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) = 0 := by
    have hkn := congrArg (fun f ↦ f ≫ Pi.π
      (fun j : ℕ ↦ cokernel (ell ^ (j + 1) • 𝟙 M)) n) hk
    simp only [Preadditive.comp_sub, Preadditive.sub_comp,
      Category.comp_id, Category.assoc, zero_comp,
      CategoryTheory.OriginalIntegralQuotientSequence.shift, Pi.lift_π] at hkn
    rw [Preadditive.sub_comp, sub_eq_zero]
    calc
      a (n + 1) ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) =
          (a (n + 1) ≫ cokernel.π (ell ^ (n + 1 + 1) • 𝟙 M)) ≫
            CategoryTheory.OriginalIntegralQuotientSequence.transition ell n M := by
        rw [Category.assoc,
          CategoryTheory.OriginalIntegralQuotientSequence.projection_transition]
      _ = (k ≫ Pi.π _ (n + 1)) ≫
          CategoryTheory.OriginalIntegralQuotientSequence.transition ell n M := by
        rw [ha (n + 1)]
      _ = k ≫ Pi.π _ n := by
        rw [Category.assoc]
        exact (sub_eq_zero.mp hkn).symm
      _ = a n ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) := (ha n).symm
  have hall (n m : ℕ) (hnm : n ≤ m) :
      a m ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) =
        a n ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih =>
      have hstep := quotientAgreement_down
        (fun j ↦ cokernel (ell ^ (j + 1) • 𝟙 M))
        (fun j ↦ cokernel.π (ell ^ (j + 1) • 𝟙 M))
        (fun j ↦ CategoryTheory.OriginalIntegralQuotientSequence.transition ell j M)
        (fun j ↦ CategoryTheory.OriginalIntegralQuotientSequence.projection_transition ell j M)
        n m hnm (a (m + 1)) (a m)
        (sub_eq_zero.mp (by simpa only [Preadditive.sub_comp] using hcompat m))
      exact hstep.trans ih
  obtain ⟨g, hg⟩ := originalIntegralOrdinaryQuotient_compatibleLimit
    ell E X M hM a hall
  refine ⟨g, ?_⟩
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc,
    CategoryTheory.OriginalIntegralQuotientSequence.augmentation, Pi.lift_π]
  rw [hg n, ha n]

end AlgebraicGeometry.ProEtale.CondensedRing
