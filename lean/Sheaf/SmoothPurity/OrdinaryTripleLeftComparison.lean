/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.SmoothPurity.OrdinaryProductTransposeData

/-! # Left triple pullback-tensor comparison
Source: blueprint relative Kunneth coherence proof, associativity clause
(blueprint: lem-pur-ordinary-triple-left-comparison). -/

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

/-- The two nested binary evaluations on the left are the single ordered triple
evaluation. This concerns only pullback and tensor comparisons and arbitrary maps;
there are no products of pushforwards or adjunctions in the assertion.
Source: lem-pur-ordinary-triple-product-transpose, proof step 6; blueprint relative
Kunneth coherence proof, clause (ii)
(blueprint: lem-pur-ordinary-triple-left-comparison).

Proof: expand both binary evaluations. Pullback-tensor naturality moves the inner
comparison and the two maps through the outer tensor comparison. Its compatibility
with composition identifies the tensor comparison of a followed by p₂ followed by f₂
with the composite comparisons. The three-map pullback cocycle identifies the two
factorizations to each of X₁ and X₂; naturality in the equality square uses square₁₂.w.
The factor to X₃ is already the specified factor through c. Tensor bifunctoriality
combines the three maps into their left-associated tensor. After the specified left
external-tensor identification this is exactly ordinaryTripleEvaluation. -/
theorem ordinaryTripleLeftComparison :
    (leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) d.squareL.w).hom.app
        ((F₁ ⊗ F₂) ⊗ F₃) ≫
      P.ordinaryBinaryEvaluation d.squareL (F₁ ⊗ F₂) F₃
        (P.ordinaryExternal d.p₁ d.p₂ K L) M
        (P.ordinaryBinaryEvaluation d.square₁₂ F₁ F₂ K L x y) z ≫
      (P.ordinaryTripleLeftIdentification d K L M).hom =
    P.ordinaryTripleEvaluation d K L M F₁ F₂ F₃ x y z := by sorry

end WeilConjectures.PurityFiniteSetting
