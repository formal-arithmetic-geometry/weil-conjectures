/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarResidueLayers
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarRegularTensorComparison
import Mathlib.Data.Int.Interval

/-! # Uniform constructibility of finite scalar tensor levels

## References

* B. Bhatt, P. Scholze, *The pro-étale topology for schemes*, Proposition 3.5.1
-/

@[expose] public section
set_option autoImplicit false

universe d u
open CategoryTheory AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- Finite scalar tensor levels have the same constructibility interval as the residue level. -/
theorem integralScalarFiniteLevel_bounds
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (r s : ℤ) (hrs : r ≤ s)
    (h₁ : intrinsicFiniteTorsionConstructible l E 1 (by omega) Y
      ((integralDerivedReduction l E Y D hl 0).obj (DerivedCategory.Q.obj P.obj)))
    (hbound : ∀ i : ℤ,
      i ∈ proEtaleCohomologicalSupport
        ((integralDerivedReduction l E Y D hl 0).obj (DerivedCategory.Q.obj P.obj)) →
      r ≤ i ∧ i ≤ s) :
    ∀ n : ℕ,
      intrinsicFiniteTorsionConstructible l L (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) Y
        (DerivedCategory.Q.obj ((integralScalarFiniteComplex l E L ι Y n).obj P.obj)) ∧
      ∀ i : ℤ,
        i ∈ proEtaleCohomologicalSupport
          (DerivedCategory.Q.obj ((integralScalarFiniteComplex l E L ι Y n).obj P.obj)) →
        r ≤ i ∧ i ≤ s := by
  classical
  intro n
  let := Padic.finite_coefficientExtensionRing l L (n + 1) (by omega)
  let B := ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let ρ := integralScalarRho l E L ι Y n
  let F := integralScalarPowerFiltration l L n
  have hflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite (C := Y.ProEt)
      (J := ProEt.topology Y) (R := R) (P.obj.X q) := P.property.2
  have hlayers := integralScalarResidueLayers_bounds l E L ι Y D hl P r s hrs h₁
    hbound n
  have htensor := (filteredCoefficientTensor_constructible_bounds Y B R ρ P.obj
    hflat B (n + 1) F (integralScalarPowerFiltration_antitone l L n)
    (integralScalarPowerFiltration_zero l L n) (integralScalarPowerFiltration_last l L n)
    r s hrs hlayers).2
  let K := DerivedCategory.Q.obj ((integralScalarFiniteComplex l E L ι Y n).obj P.obj)
  have hconstruct : ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y
      (Padic.coefficientExtensionRing l L (n + 1))
      ((DerivedCategory.homologyFunctor _ i).obj K) := by
    intro i
    exact (integralScalarRegularTensorComparison l E L ι Y P.obj n i).1.mp
      (htensor i).1
  have hzero : ∀ i : ℤ, (i < r ∨ s < i) →
      CategoryTheory.Limits.IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
    intro i hi
    exact (integralScalarRegularTensorComparison l E L ι Y P.obj n i).2.mp
      ((htensor i).2 hi)
  have hsupport : ∀ i : ℤ, i ∈ proEtaleCohomologicalSupport K → r ≤ i ∧ i ≤ s := by
    intro i hi
    change ¬ CategoryTheory.Limits.IsZero
      ((DerivedCategory.homologyFunctor _ i).obj K) at hi
    constructor
    · by_contra h
      exact hi (hzero i (Or.inl (by omega)))
    · by_contra h
      exact hi (hzero i (Or.inr (by omega)))
  constructor
  · change Set.Finite (proEtaleCohomologicalSupport K) ∧ _
    exact ⟨(Set.finite_Icc r s).subset (fun i hi ↦ hsupport i hi), hconstruct⟩
  · exact hsupport

end WeilConjectures
