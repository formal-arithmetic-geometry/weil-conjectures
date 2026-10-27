/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.RationalEvaluationData

/-! # Rational descent of completed evaluation

Source: blueprint, sec-six-functors/sk-prop-sf-dualizable-biduality, first proof paragraph
(blueprint: lem-sf-completed-evaluation-rational-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.Pretriangulated.Opposite
namespace WeilConjectures.IntegralOnSlice

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : AlgebraicGeometry.Scheme.{t}) (U : Option X.ProEt)

/-- Descend an integral exact linear comparison to the scalar localization.
Source: Stacks 05R2, 05R6; blueprint rational evaluation proof, Step 8.
(blueprint: lem-sf-completed-evaluation-rational-descent)

Proof: extend each linear contravariant functor to scalar fractions by
F(Q(f)/t^n)=Q(F(f))/t^n. Linearity proves independence of representatives,
composition, and naturality of the extended comparison. Extend the shift isomorphisms
by the same formula. The integral shift square gives the rational shift square.
Every distinguished rational triangle is isomorphic to an integral image by the
specified triangulation, so the two descended functors are triangulated. The
comparison is defined by Q(alpha), hence satisfies the displayed intertwining equation.
No assertion about the isomorphism locus is used in this descent. -/
theorem completedEvaluation_rationalDescent
    [HasZeroObject (Rational l E X U)] [HasShift (Rational l E X U) ℤ]
    [∀ n : ℤ, (shiftFunctor (Rational l E X U) n).Additive]
    [Pretriangulated (Rational l E X U)] [IsTriangulated (Rational l E X U)]
    [(q l E X U).CommShift ℤ] [(q l E X U).IsTriangulated]
    (_hshift : shiftFunctor (Rational l E X U) (1 : ℤ) =
      ScalarLocalization.map (Padic.coefficientExtensionIntegers l E) (D l E X U)
        (Padic.coefficientExtensionUniformizer l E) (shiftFunctor (D l E X U) (1 : ℤ)))
    (_hQshift : ∀ L : D l E X U,
      HEq (((q l E X U).commShiftIso (1 : ℤ)).hom.app L)
        (𝟙 ((q l E X U).obj ((shiftFunctor (D l E X U) (1 : ℤ)).obj L))))
    (_htriangles : ∀ T : Triangle (Rational l E X U),
      T ∈ distTriang (Rational l E X U) ↔
        ∃ T' : Triangle (D l E X U), T' ∈ distTriang (D l E X U) ∧
          Nonempty (T ≅ (q l E X U).mapTriangle.obj T'))
    (M : D l E X U)
    [(phi l E X U M).Additive] [(psi l E X U M).Additive]
    [(phi l E X U M).Linear (Padic.coefficientExtensionIntegers l E)]
    [(psi l E X U M).Linear (Padic.coefficientExtensionIntegers l E)]
    [(phi l E X U M).CommShift ℤ] [(psi l E X U M).CommShift ℤ]
    [(phi l E X U M).IsTriangulated] [(psi l E X U M).IsTriangulated]
    (α : phi l E X U M ⟶ psi l E X U M) [NatTrans.CommShift α ℤ] :
    ∃ (F G : (Rational l E X U)ᵒᵖ ⥤ Rational l E X U)
            (eF : (q l E X U).op ⋙ F ≅ phi l E X U M ⋙ q l E X U)
            (eG : (q l E X U).op ⋙ G ≅ psi l E X U M ⋙ q l E X U)
            (sF : F.CommShift ℤ) (sG : G.CommShift ℤ),
            (fun [fShift : F.CommShift ℤ] [gShift : G.CommShift ℤ] ↦
              F.IsTriangulated ∧ G.IsTriangulated ∧
              ∃ αQ : F ⟶ G,
                NatTrans.CommShift αQ ℤ ∧
                Functor.whiskerLeft (q l E X U).op αQ ≫ eG.hom =
                  eF.hom ≫ Functor.whiskerRight α (q l E X U))
              (fShift := sF) (gShift := sG) := by sorry

end WeilConjectures.IntegralOnSlice
