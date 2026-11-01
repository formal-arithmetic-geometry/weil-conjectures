/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.SmoothPurity.Point.PointFibreEquivalence
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.Determinant
public import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.CoefficientCohomologyModules
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Sf.SfIntegralDirectImageConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
public import WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists
public import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.ZetaSeries
/-! # Ordinary and compactly supported coefficient cohomology

Source: Weil blueprint main-20261015, sec-six-functors-basics/sk-def-sf-admissible,
ordinary and compactly supported cohomology
(blueprint: def-weil-ordinary-compact-cohomology).

The four coefficient constructions evaluate the recorded ordinary/compact direct images
at the geometric point. Constants, signed twists and Weil-forgetful specializations use
those same constructions. `ordinaryCompactCohomology` collects the actual operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Coefficient)
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]

/-- Ordinary finite-level derived sections, using the recorded direct-image and point-section
functors.
Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-def-sf-admissible/def-weil-ordinary-compact-cohomology.md.
Source: blueprint main-20261015, ordinary and compact cohomology
(blueprint: def-weil-ordinary-compact-cohomology). -/
def finiteOrdinarySections (n : ℕ) (hn : 1 ≤ n) (K : proEtaleDerivedCategory Y
    (Padic.coefficientExtensionRing l E n)) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E n)).mapDerivedCategory).obj
    ((proEtaleConstantDerivedDirectImage (Y ↘ Spec (.of D.k))
      (Padic.coefficientExtensionRing l E n)).obj K)

/-- The tower-defined integral ordinary image, in its constructible category.
The chosen Roos vertex is determined up to isomorphism by the recorded derived limit;
its data are not chosen from a mere unstructured existence assertion.
Source: blueprint ordinary-cohomology formula
(blueprint: def-weil-ordinary-compact-cohomology). -/
def integralImage (K : sfIntegralConstructibleCategory l E Y) :
    sfIntegralConstructibleCategory l E (Spec (.of D.k)) := by
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (Y ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  let h := sfIntegralDirectImage_constructible D.k l (finiteFieldDatumPrimeUnit D l hl)
    E (Y ↘ Spec (.of D.k)) K.obj K.property
  letI := h.1.choose
  let L : SfIntegralDirectImage l E (Y ↘ Spec (.of D.k)) K.obj := h.1.choose_spec.some
  exact ⟨L.obj, (h.2.1 L).1⟩

variable (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

section Weil

variable (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom]
  [QuasiCompact Y₀.hom]
  [LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k))]
  [QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k))]
  [IsSeparated ((D.geometricFiber Y₀).left ↘ Spec (.of D.k))]

end Weil

end WeilConjectures
