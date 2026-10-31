/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ClosedEvaluationDualCriterion
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! # Duality from a symmetric closed evaluation comparison

Source: literature/stacks-project/sites-cohomology.tex, Tag 0FPU, example-dual-derived,
the two omitted triangle verifications (blueprint: lem-pod-closed-evaluation-dual-criterion).
The existing `closedEvaluationComparison` is used with evaluation `(β_ P D).hom ≫ e`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

/-- The specified coevaluation obtained by transposing the right unitor, inverting
its evaluation comparison, and applying the symmetry.

Source: Stacks Project, sites-cohomology.tex, Tag 0FPU, example-dual-derived,
the definition of eta (blueprint: lem-pod-closed-evaluation-dual-criterion). -/
noncomputable def symmetricClosedEvaluationCoevaluation
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] (P D : C) (e : D ⊗ P ⟶ 𝟙_ C)
    [IsIso (closedEvaluationComparison MonoidalClosed.internalHomAdjunction₂
      P D ((β_ P D).hom ≫ e) P)] : 𝟙_ C ⟶ P ⊗ D :=
  closedEvaluationCoevaluation MonoidalClosed.internalHomAdjunction₂
    P D ((β_ P D).hom ≫ e) ≫ (β_ D P).hom

/-- The evaluation and its specified coevaluation satisfy both duality triangles.

Source: Stacks Project, Tag 0FPU, example-dual-derived, the omitted triangle checks
(blueprint: lem-pod-closed-evaluation-dual-criterion).

Proof:
1. Write t_N for the composite before transposition. The definition of the existing
   comparison gives uncurry(phi_N) = t_N and naturality in N. Put q = inv(phi_P)
   and u_P = curry(rho_P). The specified coevaluation is u_P followed by q and beta(D,P).
2. Let L_P be the first displayed triangle composite. Curry L_P after the right
   unitor. The unit-braiding identity replaces lambda_P.inv after rho_P.hom by
   beta(P,1). Braiding naturality moves the coevaluation through this braiding;
   the hexagon and associator coherence identify the resulting contraction with
   t_P after P tensored with beta(P,D) followed by c. Symmetry cancels the two
   braidings, so the transpose is u_P followed by q and phi_P, hence u_P.
   Injectivity of transposition and cancellation of rho_P give L_P = identity.
3. The function sending x : D → D to (x tensor P) followed by e is injective:
   after precomposing with beta(P,D), its transpose is x followed by rho_D.inv
   and phi_1, a composite with an isomorphism. Let L_D be the second triangle.
   Both e after (L_D tensor P) and e after (D tensor L_P) equal the contraction
   of the two consecutive pairs in (D tensor P) tensor (D tensor P), after
   inserting c between D and P. Tensor bifunctoriality gives the two orders of
   contraction; associator naturality and the pentagon and unit triangle give
   the required reparenthesizations. Thus these two maps agree. Since L_P is
   identity, evaluation injectivity gives L_D = identity.
4. These are exactly the dual-pair triangle equations, with the specified e and c.
-/
theorem symmetric_closed_evaluation_dual_criterion
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] (P D : C) (e : D ⊗ P ⟶ 𝟙_ C)
    [∀ N : C, IsIso (closedEvaluationComparison MonoidalClosed.internalHomAdjunction₂
      P D ((β_ P D).hom ≫ e) N)] :
    ((λ_ P).inv ≫ symmetricClosedEvaluationCoevaluation P D e ▷ P ≫
      (α_ P D P).hom ≫ P ◁ e ≫ (ρ_ P).hom = 𝟙 P) ∧
    ((ρ_ D).inv ≫ D ◁ symmetricClosedEvaluationCoevaluation P D e ≫
      (α_ D P D).inv ≫ e ▷ D ≫ (λ_ D).hom = 𝟙 D) := by
  sorry

end CategoryTheory
