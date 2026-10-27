/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.Paper.FdRawLocalizationScalarCoherence

/-! # Packaging raw scalar comparisons on the specified stage systems

Source: trace-definition coefficient-category comparison, localization step 7
(blueprint: lem-fd-raw-scalar-comparison-packaging).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe d u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.FdRawLocalization
namespace WeilConjectures

/-- Convert an already coherent raw inverse comparison into a morphism of the specified
stage systems. This is only presentation transport and inversion of the integral-lift square;
existence of the integral comparison and existence of the raw comparison are inputs.
Source: trace-definition final coefficient-category sentence, localization step 7
(blueprint: lem-fd-raw-scalar-comparison-packaging).

Proof: The specification of GeneralAlgebraicallyClosedCoefficients.stageSystem identifies
its transition functors and associators with scalar and assoc. Transport j inverse along
these equalities. This defines beta with the arrow direction required by StageSystem.Morphism;
its finite functors are family.functor. Precompose the raw inverse cocycle with the two beta
components and cancel j against beta to obtain Morphism.coh. Transport family.shift using
its shift_identity; the stage transition shift is the canonical equality transport of the
specified scalar shift, so both beta shift squares follow from the given j shift squares.
The finite functors and their shifts agree with the supplied stage equivalences, hence are
exact. Transport the raw unit equation to beta inverse. Finally invert the supplied
integral-lift equation: localization preserves inverses and composition, so the inverse of
Q(b inverse) followed by the inverse scalar-integral comparison is the scalar-integral
comparison followed by Q(b). The supplied rational object normalizations identify the
endpoints; only their canonical equality casts occur. This gives the required forward lift.
No pentagon or four-field assertion is assumed or concluded here.
-/
theorem fdRawScalarComparisonPackaging
    (l : ℕ) [Fact l.Prime]
    (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (T : Scheme.{u}) [IsNoetherian T]
    [dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (stage : ∀ E : Padic.FiniteCoefficientFields l Ω, FdRationalStageComparison l Ω T E)
    (b : ∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
      I l Ω T stage E ⋙ C l Ω T h ≅ U l Ω T h ⋙ I l Ω T stage L)
    (family : RationalFamily l Ω T stage)
    (j : RawComparison l Ω T stage family)
    (hshift : (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
        NatTrans.CommShift (j h).hom ℤ ∧ NatTrans.CommShift (j h).inv ℤ ∧
        (scalar l Ω T h ⋙ J l Ω T stage family L).IsTriangulated ∧
        (J l Ω T stage family E ⋙ (P l Ω T).T h).IsTriangulated))
    (hlift : (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
        (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
        (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
        HEq ((j h).hom.app K')
          ((pbcStageLocalization l Ω T L).map ((b h).inv.app K) ≫
            (pbcScalarIntegralComparison l Ω T dT.out iT.out h).inv.app
              ((I l Ω T stage E).obj K))))
    (hunit : (∀ (E : Padic.FiniteCoefficientFields l Ω)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        HEq ((j (le_refl E)).hom.app K)
          ((J l Ω T stage family E).map
            ((unit l Ω T E).hom.app K))))
    (hcocycle : (∀ {E L M : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) (k : L ≤ M)
        (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
        (j k).hom.app ((scalar l Ω T h).obj K) ≫
          ((P l Ω T).T k).map ((j h).hom.app K) ≫
          ((P l Ω T).assoc h k).hom.app ((J l Ω T stage family E).obj K) =
        (J l Ω T stage family M).map ((assoc l Ω T h k).hom.app K) ≫
          (j (h.trans k)).hom.app K))
    : ∃ (F : StageSystem.Morphism
      (C := GeneralAlgebraicallyClosedCoefficients.Stage l Ω T)
      (D := pbcStageCategory l Ω T)
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω T)
      (pbcScalarSystem l Ω T dT.out iT.out))
      (s : ∀ E, (F.Φ E).CommShift ℤ),
      let _ : ∀ E, (F.Φ E).CommShift ℤ := s
      (∀ E, HEq (F.Φ E) (stage E).rational.functor) ∧
      (∀ E (n : ℤ),
    HEq ((F.Φ E).commShiftIso n) ((stage E).rational.functor.commShiftIso n)) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L),
    NatTrans.CommShift (F.β h).hom ℤ ∧ NatTrans.CommShift (F.β h).inv ℤ) ∧
      (∀ E, (F.Φ E).IsTriangulated) ∧
      (∀ (E : Padic.FiniteCoefficientFields l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq ((F.β (le_refl E)).inv.app K)
      ((F.Φ E).map
        ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω T E).hom.app K))) ∧
      (∀ {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (pbcFiniteField.{u} l Ω E) T)
    (K' : GeneralAlgebraicallyClosedCoefficients.Stage l Ω T E),
    HEq K' ((sfRationalConstructibleLocalization l (pbcFiniteField.{u} l Ω E) T).obj K) →
    HEq ((F.β h).hom.app K')
      ((pbcScalarIntegralComparison l Ω T dT.out iT.out h).hom.app
          ((stage E).integral.functor.obj K) ≫
        (pbcStageLocalization l Ω T L).map ((b h).hom.app K))) := by
  sorry

end WeilConjectures
