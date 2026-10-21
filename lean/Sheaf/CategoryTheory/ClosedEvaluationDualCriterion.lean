module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Adjunction.Parametrized

/-! # The evaluation-isomorphism criterion for a dual pair

Source: Stacks Project, sites-cohomology.tex, Tag 0FPU, example-dual-derived,
the two omitted triangle verifications (blueprint: lem-fix-closed-evaluation-dual-criterion).
The criterion uses the specified internal Hom and transposition, without symmetry.
-/

@[expose] public section

universe u v

open CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

/-- The transpose of evaluation tensored with the target.
Source: Stacks Project, Tag 0FPU, example-dual-derived, the evaluation comparison
(blueprint: lem-fix-closed-evaluation-dual-criterion). -/
def closedEvaluationComparison {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {H : Cᵒᵖ ⥤ C ⥤ C} (adj : curriedTensor C ⊣₂ H) (P D : C)
    (e : P ⊗ D ⟶ 𝟙_ C) (N : C) : D ⊗ N ⟶ (H.obj (op P)).obj N :=
  (adj.adj P).homEquiv (D ⊗ N) N
    ((α_ P D N).inv ≫ e ▷ N ≫ (λ_ N).hom)

/-- The specified coevaluation: transpose the right unitor, then invert the comparison.
Source: Stacks Project, Tag 0FPU, example-dual-derived, the definition of eta
(blueprint: lem-fix-closed-evaluation-dual-criterion). -/
noncomputable def closedEvaluationCoevaluation
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {H : Cᵒᵖ ⥤ C ⥤ C} (adj : curriedTensor C ⊣₂ H) (P D : C)
    (e : P ⊗ D ⟶ 𝟙_ C) [IsIso (closedEvaluationComparison adj P D e P)] :
    𝟙_ C ⟶ D ⊗ P :=
  (adj.adj P).homEquiv (𝟙_ C) P (ρ_ P).hom ≫ inv (closedEvaluationComparison adj P D e P)

/-- The specified evaluation and coevaluation satisfy both duality triangles.
Source: Stacks Project, Tag 0FPU, example-dual-derived, the omitted triangle checks
(blueprint: lem-fix-closed-evaluation-dual-criterion).

Proof:
1. Write E_N for the uncurried comparison. The definition of c gives c ≫ phi_P = u_P.
   Naturality and injectivity of transposition yield P ◁ c ≫ E_P = (rho_P).hom.
   Precompose with the inverse right unitor to obtain the first triangle.
2. The isomorphism a = (rho_D).inv ≫ phi_1 is the transpose of e: expand E_1,
   use naturality of the right unitor and equality of the two unitors on the unit,
   and cancel the adjacent unitors. These are monoidal unit identities from
   def-sfb-monoidal-category.
3. Let g be the second triangle composite and t the first. Tensor bifunctoriality
   identifies the two contractions of the disjoint consecutive pairs in
   P tensor D tensor P tensor D. After inserting P tensor c tensor D, this says
   P ◁ g ≫ e = t ▷ D ≫ e = e, since Step 1 gives t = identity.
   Associator and unitor naturality inserts the displayed constraints; no factors move.
4. Transposition and Step 2 give g ≫ a = a. Cancel the isomorphism a to obtain
   g = identity. Together these are precisely the dual-pair axioms for e and c.
All structural calculations use def-sfb-monoidal-category. -/
theorem closed_evaluation_dual_criterion
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {H : Cᵒᵖ ⥤ C ⥤ C} (adj : curriedTensor C ⊣₂ H) (P D : C)
    (e : P ⊗ D ⟶ 𝟙_ C)
    [∀ N : C, IsIso (closedEvaluationComparison adj P D e N)] :
    ((ρ_ P).inv ≫ P ◁ closedEvaluationCoevaluation adj P D e ≫
      (α_ P D P).inv ≫ e ▷ P ≫ (λ_ P).hom = 𝟙 P) ∧
    ((λ_ D).inv ≫ closedEvaluationCoevaluation adj P D e ▷ D ≫
      (α_ D P D).hom ≫ D ◁ e ≫ (ρ_ D).hom = 𝟙 D) := by
  sorry

end CategoryTheory
