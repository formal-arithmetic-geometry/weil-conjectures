/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.FdRawLocalization.FdRawLocalizationScalarData

/-! # Descent of the fixed integral scalar comparison

Source: trace-definition coefficient-category sentence, raw localization steps 1--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.FdRawLocalization

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (T : Scheme.{u}) [IsNoetherian T]
  [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)

/-- Integral cocycle and unit equations descend for a component-normalized comparison.
Source: raw localization scalar-descent steps 2 and 3
(blueprint: lem-fd-raw-normalized-comparison-coherence).

Proof: Every raw rational object is the image of its underlying integral object.
Evaluate the desired three-field identity on that object and substitute hcomponents
for each comparison. Naturality of pbcScalarIntegralComparison moves the localized
inverse b component through the PBC scalar functor. The defining normalization of
pbcScalarAssociator cancels its adjacent integral comparisons and identifies the
remaining associator with Q of pbcIntegralScalarAssociator. The framework associator
is sfRationalScalarComp followed by coefficient-inclusion equality transport; its
normalization identifies it with Q of integralAssoc. The stage tensor formula moves
this last map through J. What remains is Q applied to hcocycle, followed by the same
invertible scalar comparison on both sides; preservation of composition gives the
equality. At equal fields the PBC transition is literally the identity. Its integral
comparison is the localization of the actual integral unit, so hunit gives the
identity value after the framework unit normalization. Finally specialize the
three-field identity to an identity inclusion in the first and second position.
The balanced-tensor left and right unit equations for sfRationalScalarComp, including
the coefficient-inclusion equality transports, turn those two specializations into
the displayed unit equations. These normalizations retain the actual completeness
map. All arguments include repeated fields, zero objects, and the empty scheme. -/
theorem rawNormalizedComparisonCoherence
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (hcocycle : ∀ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      (b k).inv.app ((U l Ω T h).obj K) ≫
        (C l Ω T k).map ((b h).inv.app K) ≫
        (pbcIntegralScalarAssociator l Ω T dT.out iT.out h k).hom.app
          ((I l Ω T stage E).obj K) =
      (I l Ω T stage M).map ((integralAssoc l Ω T h k).hom.app K) ≫
        (b (h.trans k)).inv.app K)
    (hunit : ∀ (E : Padic.FiniteCoefficientFields l Ω)
      (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T),
      (b (le_refl E)).inv.app K ≫
        (pbcIntegralScalarUnit l Ω T dT.out iT.out E).hom.app ((I l Ω T stage E).obj K) =
      (I l Ω T stage E).map ((integralUnit l Ω T E).hom.app K))
    (family : RationalFamily l Ω T stage)
    (j : RawComparison l Ω T stage family)
    (hcomponents : (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
        (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
        HEq ((j h).hom.app K')
          ((pbcStageLocalization l Ω T L).map ((b h).inv.app K) ≫
            (pbcScalarIntegralComparison l Ω T dT.out iT.out h).inv.app
              ((I l Ω T stage E).obj K)))) :
    (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq ((j (le_refl E)).hom.app K)
          ((J l Ω T stage family E).map
            ((unit l Ω T E).hom.app K))) ∧
      (∀ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (j k).hom.app ((scalar l Ω T h).obj K) ≫
          ((P l Ω T).T k).map ((j h).hom.app K) ≫
          ((P l Ω T).assoc h k).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family M).map ((assoc l Ω T h k).hom.app K) ≫
          (j (h.trans k)).hom.app K) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (j h).hom.app ((scalar l Ω T (le_refl E)).obj K) ≫
          ((P l Ω T).T h).map ((j (le_refl E)).hom.app K) ≫
          ((P l Ω T).assoc (le_refl E) h).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family L).map ((scalar l Ω T h).map
          ((unit l Ω T E).hom.app K)) ≫
          (j h).hom.app K) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (j (le_refl L)).hom.app ((scalar l Ω T h).obj K) ≫
          ((P l Ω T).T (le_refl L)).map ((j h).hom.app K) ≫
          ((P l Ω T).assoc h (le_refl L)).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family L).map
          ((unit l Ω T L).hom.app
            ((scalar l Ω T h).obj K)) ≫ (j h).hom.app K) := by sorry

end WeilConjectures.FdRawLocalization
