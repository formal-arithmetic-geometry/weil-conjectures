/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralOrdinaryQuotientCompatibleLimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralOrdinaryQuotientKernelSeparated
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleObjectProductsExact
import Mathlib.CategoryTheory.Abelian.Refinements

/-! # Finite approximation in the ordinary quotient tower -/

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

/-- A single finite approximation to a compatible ordinary quotient family.

Source: Hemo--Richarz--Scholbach, Propositions 5.1 and 7.6 and Theorem 7.7;
Bhatt--Scholze, Section 6.1.
(blueprint: lem-sp-original-integral-ordinary-quotient-finite-lifts).

Exact countable products make the product of the quotient projections epimorphic.
Pull it back along the compatible family to obtain one epimorphic refinement on
which every quotient component has an integral lift. Compatibility of the family
makes these lifts Cauchy. Apply the existing compatible-limit theorem on that
refinement. The resulting integral map kills the kernel of the refinement:
every quotient of its restriction to the kernel vanishes, so separatedness
applies. Descend along the epimorphism and retain any specified quotient component.
-/
theorem originalIntegralOrdinaryQuotient_finiteLifts
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
    ∀ n : ℕ, ∃ a : W ⟶ M,
      a ≫ cokernel.π (ell ^ (n + 1) • 𝟙 M) =
        k ≫ Pi.π (fun j : ℕ ↦ cokernel (ell ^ (j + 1) • 𝟙 M)) n := by
  classical
  let B := condensedRingObj (Profinite.padicIntegersRingObj ell E) X
  let C := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) B
  let : HasExactLimitsOfShape (Discrete (ULift.{u + 1} ℕ)) C :=
    proEtale_moduleObject_products_exact X B (ULift.{u + 1} ℕ)
  let : HasExactLimitsOfShape (Discrete ℕ) C :=
    HasExactLimitsOfShape.of_domain_equivalence C
      (Discrete.equivalence Equiv.ulift)
  let Q := fun n : ℕ ↦ cokernel (ell ^ (n + 1) • 𝟙 M)
  let q : ∀ n : ℕ, M ⟶ Q n := fun n ↦ cokernel.π (ell ^ (n + 1) • 𝟙 M)
  have hqepi : Epi (Limits.Pi.map q) := by
    let f : Discrete.functor (fun _ : ℕ ↦ M) ⟶ Discrete.functor Q :=
      Discrete.natTrans (fun n ↦ q n.as)
    have hcomp : ∀ i : Discrete ℕ, Epi (f.app i) := fun i ↦ by
      change Epi (cokernel.π (ell ^ (i.as + 1) • 𝟙 M))
      infer_instance
    let : ∀ i : Discrete ℕ, Epi (f.app i) := hcomp
    have hf : Epi f := NatTrans.epi_of_epi_app f
    change Epi (lim.map f)
    infer_instance
  obtain ⟨P, p, hp, y, hy⟩ := surjective_up_to_refinements_of_epi (Limits.Pi.map q) k
  let a : ℕ → (P ⟶ M) := fun n ↦ y ≫ Pi.π (fun _ : ℕ ↦ M) n
  have ha (n : ℕ) : a n ≫ q n = p ≫ k ≫ Pi.π Q n := by
    have h := congrArg (fun f ↦ f ≫ Pi.π Q n) hy.symm
    simpa only [Category.assoc, Limits.Pi.map_π, a] using h
  have hstep (n : ℕ) :
      k ≫ Pi.π Q (n + 1) ≫
        CategoryTheory.OriginalIntegralQuotientSequence.transition ell n M =
      k ≫ Pi.π Q n := by
    have h := congrArg (fun f ↦ f ≫ Pi.π Q n) hk
    dsimp only [Q] at h ⊢
    simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Category.assoc, zero_comp,
      CategoryTheory.OriginalIntegralQuotientSequence.shift, Pi.lift_π] at h
    exact (sub_eq_zero.mp h).symm
  have hadj (n : ℕ) : a (n + 1) ≫ q n = a n ≫ q n := by
    calc
      a (n + 1) ≫ q n = (a (n + 1) ≫ q (n + 1)) ≫
          CategoryTheory.OriginalIntegralQuotientSequence.transition ell n M := by
        simp only [q, Category.assoc,
          CategoryTheory.OriginalIntegralQuotientSequence.projection_transition]
      _ = (p ≫ k ≫ Pi.π Q (n + 1)) ≫
          CategoryTheory.OriginalIntegralQuotientSequence.transition ell n M := by
        rw [ha]
      _ = p ≫ k ≫ Pi.π Q n := by
        rw [Category.assoc, Category.assoc, hstep]
      _ = a n ≫ q n := (ha n).symm
  have hcompat (n m : ℕ) (hnm : n ≤ m) : a m ≫ q n = a n ≫ q n := by
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih =>
      have hdown := quotientAgreement_down Q q
        (fun j ↦ CategoryTheory.OriginalIntegralQuotientSequence.transition ell j M)
        (fun j ↦ CategoryTheory.OriginalIntegralQuotientSequence.projection_transition ell j M)
        n m hnm (a (m + 1)) (a m) (hadj m)
      exact hdown.trans ih
  obtain ⟨g, hg⟩ := originalIntegralOrdinaryQuotient_compatibleLimit ell E X M hM a hcompat
  have hgq (n : ℕ) : g ≫ q n = p ≫ k ≫ Pi.π Q n := (hg n).trans (ha n)
  have hker : kernel.ι p ≫ g = 0 := by
    apply originalIntegralOrdinaryQuotientKernel_separated ell E X M hM
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc,
      CategoryTheory.OriginalIntegralQuotientSequence.augmentation, Pi.lift_π, zero_comp]
    change kernel.ι p ≫ g ≫ q n = 0
    rw [hgq, ← Category.assoc (kernel.ι p) p, kernel.condition]
    simp
  let b := Abelian.epiDesc p g hker
  intro n
  refine ⟨b, ?_⟩
  apply (cancel_epi p).1
  rw [← Category.assoc, Abelian.comp_epiDesc]
  exact hgq n

end AlgebraicGeometry.ProEtale.CondensedRing
