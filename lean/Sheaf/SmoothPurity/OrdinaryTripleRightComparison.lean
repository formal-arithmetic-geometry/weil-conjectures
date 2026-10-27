/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.SmoothPurity.OrdinaryProductTransposeData

/-! # Right triple pullback-tensor comparison
Source: blueprint relative Kunneth coherence proof, associativity clause
(blueprint: lem-pur-ordinary-triple-right-comparison). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurityFiniteSetting
variable (P : PurityFiniteSetting.{u})
variable {X₁ X₂ X₃ B : Scheme.{u}} {f₁ : X₁ ⟶ B} {f₂ : X₂ ⟶ B} {f₃ : X₃ ⟶ B}
    (d : OrdinaryTripleProductDiagram f₁ f₂ f₃)
    (K : P.ordinaryCategory X₁) (L : P.ordinaryCategory X₂) (M : P.ordinaryCategory X₃)
    (F₁ F₂ F₃ : P.ordinaryCategory B)
    (x : (P.ordinaryPull f₁).obj F₁ ⟶ K)
    (y : (P.ordinaryPull f₂).obj F₂ ⟶ L)
    (z : (P.ordinaryPull f₃).obj F₃ ⟶ M)

/-- The two nested binary evaluations on the right are the same ordered triple
evaluation after the specified associators and projection equalities. The inputs
and the three maps are arbitrary, independently of every direct-image product.
Source: lem-pur-ordinary-triple-product-transpose, proof step 7; blueprint relative
Kunneth coherence proof, clause (ii)
(blueprint: lem-pur-ordinary-triple-right-comparison).

Proof: expand the two binary evaluations. Naturality moves the inner tensor
comparison through the pullback along b. Pullback composition coherence and the
three-map cocycle identify the factors along b followed by q₂ and q₃ with the
specified projections a followed by p₂ and c. The first factor is a followed by p₁;
the equality of its composite with the structure map uses squareR.w and square₁₂.w.
Associativity compatibility of the pullback-tensor comparison moves the source
associator to the target. It cancels the inverse associator in the right external
tensor identification. Associator naturality then leaves the same left-associated
ordered tensor of the three pulled-back maps as ordinaryTripleEvaluation. -/
theorem ordinaryTripleRightComparison :
    (leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient)
      (d.squareR.w.symm.trans ((Category.assoc d.a d.p₁ f₁).trans
        (congrArg (fun z ↦ d.a ≫ z) d.square₁₂.w))).symm).hom.app ((F₁ ⊗ F₂) ⊗ F₃) ≫
      (P.ordinaryPull (d.b ≫ (d.q₂ ≫ f₂))).map (α_ F₁ F₂ F₃).hom ≫
      P.ordinaryBinaryEvaluation d.squareR F₁ (F₂ ⊗ F₃) K
        (P.ordinaryExternal d.q₂ d.q₃ L M) x
        ((leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient)
          d.square₂₃.w).hom.app (F₂ ⊗ F₃) ≫
          P.ordinaryBinaryEvaluation d.square₂₃ F₂ F₃ L M y z) ≫
      (P.ordinaryTripleRightIdentification d K L M).hom =
    P.ordinaryTripleEvaluation d K L M F₁ F₂ F₃ x y z := by sorry

end WeilConjectures.PurityFiniteSetting
