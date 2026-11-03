/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralTowerInverseImageUnit
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-!
# The strict Roos lift of the integral inverse-image comparison

Source: Stacks Project, Tags 03D6, 06YY and 0941
(blueprint: lem-trf-integral-pullback-reduction-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- The defining Roos lift of the inverse-image comparison is the limit lift of the
inverse image of a strict quotient presentation, followed by the whole-tower tensor
unit and the normalized pullback tower identification.

Source: Stacks Project, Tags 03D6, 06YY and 0941; Steps 3 and 5 of the
resolution-matching argument (blueprint: lem-trf-integral-pullback-reduction-counit).

Proof: both sides are maps into a Roos cone, so they are determined by their
unshifted coordinates and their shifted coordinate. The shifted coordinates vanish
for both. In the unshifted coordinate at level n, the left side is theta_n. On a
section x over U, the right side sends x to b(x), which is the strict reduction of
the tensor generator 1 tensor x, then inserts the sequence-pullback generator and
restricts along the comma arrow of U, and finally applies q. By the generator
formula for q and naturality of q under restriction this is the restriction of the
finite pullback generator of 1 tensor x, which is the defining formula of theta_n. -/
theorem inverseImageRoosComparisonComplex_eq_limitToRoos
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {W Z : Scheme.{u}} (h : Z ⟶ W) [IsIso h]
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P)
    (b : ((Functor.const ℕᵒᵖ : scalarReductionSource l E W ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E W).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)
    (hb : ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ) (x : (P.X i).val.obj U),
      (((b.f i).app (op n)).val.app U) x =
        integralComparisonRestrictedSection l E W (C.X i) n U
          (integralComparisonSequenceSection l E W (C.X i) n U
            (((κ n).inv.f i).val.app U
              (unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x))))
    (q : (((coefficientSequenceRestriction l E Z).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E h).mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l E h).obj P)
    (hq : ∀ (n : ℕ) (i : ℤ) (U : W.ProEt)
        (x : (C.X i).val.obj (op (n, U))),
        ((q.hom.app (op n)).f i).val.app (op ((proEtaleBaseChange h).obj U))
          (integralComparisonRestrictedSection l E Z
            ((integralComparisonSequencePullback l E h).obj (C.X i)) n
            (op ((proEtaleBaseChange h).obj U))
            (integralComparisonSequenceGenerator l E h (C.X i) n U x)) =
          integralOperationsPullbackGenerator l E h n
            (((unrestrictedIntegralFiniteComplex l E W n).obj P).X i) U
            (((κ n).hom.f i).val.app (op U)
              (coefficientEvaluationSection l E W (C.X i) n (op U) x))) :
    inverseImageRoosComparisonComplex l E h P =
      ((constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E Z)).mapHomologicalComplex
          (.up ℤ)).homEquiv _ _
        ((NatTrans.mapHomologicalComplex
            (Functor.compConstIso ℕᵒᵖ (inverseImageIntegralModules l E h)).hom (.up ℤ)).app P ≫
          ((integralTowerInverseImage l E h).mapHomologicalComplex (.up ℤ)).map b ≫
          (NatTrans.mapHomologicalComplex (integralTowerInverseImageUnit l E h).hom
            (.up ℤ)).app C) ≫
        integralComparisonLimitToRoos l E Z _ ≫ integralOperationsRoosFunctor.map q.hom := by
  sorry

end WeilConjectures
