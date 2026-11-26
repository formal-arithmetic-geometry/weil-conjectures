/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.FilteredCoefficientTensorBounds
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarResidueLayerConstructible
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarResidueLayerVanishing

/-! # The residue layers of the target coefficient filtration

We filter the finite target coefficient ring by the powers of a uniformizer and show that each
successive layer tensor has constructible cohomology in the residue interval.

## References

* Stacks Project, Modules on Sites (tensor products of locally constant sheaves) and
  Pro-étale Cohomology (constructible complexes form a Serre subcategory).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe d u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- The actual power ideals in the finite target ring, regarded as submodules. -/
def integralScalarPowerFiltration (n : ℕ) :
    Fin (n + 1 + 1) → Submodule
      (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1)))
      (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))) :=
  fun j ↦ (Ideal.span ({ULift.up ((Ideal.Quotient.mk
    (Padic.coefficientExtensionIdeal l L (n + 1)))
      (Padic.coefficientExtensionUniformizer l L))} :
        Set (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))))) ^ (j : ℕ)

/-- Power ideals decrease with the exponent. -/
theorem integralScalarPowerFiltration_antitone (n : ℕ) :
    Antitone (integralScalarPowerFiltration l L n) := by
  intro i j hij
  exact Ideal.pow_le_pow_right hij

/-- The first power ideal is the whole coefficient module. -/
theorem integralScalarPowerFiltration_zero (n : ℕ) :
    integralScalarPowerFiltration l L n 0 = ⊤ := by
  simp [integralScalarPowerFiltration]

/-- The last power ideal vanishes in the defining quotient. -/
theorem integralScalarPowerFiltration_last (n : ℕ) :
    integralScalarPowerFiltration l L n (Fin.last (n + 1)) = ⊥ := by
  have hz : ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1)))
      (Padic.coefficientExtensionUniformizer l L)) ^ (n + 1) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  change ((Ideal.span ({ULift.up ((Ideal.Quotient.mk
    (Padic.coefficientExtensionIdeal l L (n + 1)))
      (Padic.coefficientExtensionUniformizer l L))} :
        Set (ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))))) ^
          (n + 1) : Ideal _) = ⊥
  rw [Ideal.span_singleton_pow]
  have hu : (ULift.up ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1)))
      (Padic.coefficientExtensionUniformizer l L)) :
        ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))) ^ (n + 1) = 0 := by
    apply ULift.ext
    exact hz
  rw [hu, Ideal.span_singleton_zero]

/-- Each successive layer tensor has constructible cohomology in the residue interval. -/
theorem integralScalarResidueLayers_bounds
    (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (r s : ℤ) (hrs : r ≤ s)
    (h₁ : intrinsicFiniteTorsionConstructible l E 1 (by omega) Y
      ((integralDerivedReduction l E Y D hl 0).obj (DerivedCategory.Q.obj P.obj)))
    (hbound : ∀ i : ℤ,
      i ∈ proEtaleCohomologicalSupport
        ((integralDerivedReduction l E Y D hl 0).obj (DerivedCategory.Q.obj P.obj)) →
      r ≤ i ∧ i ≤ s) (n : ℕ) :
    letI := Padic.finite_coefficientExtensionRing l L (n + 1) (by omega)
    let B := ULift.{u + 1} (Padic.coefficientExtensionRing l L (n + 1))
    let F := integralScalarPowerFiltration l L n
    ∀ (j : Fin (n + 1)) (i : ℤ),
      IsConstructibleProEtaleCoefficientModuleSheaf Y B
        ((filteredCoefficientTensorComplex Y B
          (completedIntegralCommRingSheafUnrestricted l E Y)
          (integralScalarRho l E L ι Y n) P.obj
          (ModuleCat.of B ((F j.castSucc) ⧸
            (F j.succ).comap (F j.castSucc).subtype))).homology i) ∧
      ((i < r ∨ s < i) → IsZero
        ((filteredCoefficientTensorComplex Y B
          (completedIntegralCommRingSheafUnrestricted l E Y)
          (integralScalarRho l E L ι Y n) P.obj
          (ModuleCat.of B ((F j.castSucc) ⧸
            (F j.succ).comap (F j.castSucc).subtype))).homology i)) := by
  have hc := integralScalarResidueLayer_constructible l E L ι Y D hl P r s hrs h₁
    hbound n (integralScalarPowerFiltration l L n) rfl
  have hz := integralScalarResidueLayer_vanishing l E L ι Y D hl P r s hrs h₁
    hbound n (integralScalarPowerFiltration l L n) rfl
  dsimp only
  intro j i
  exact ⟨hc j i, hz j i⟩

end WeilConjectures
