module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Adjunction.Parametrized

/-! # Naturality of the iterated evaluation transpose

Source: Stacks Project, categories.tex, Tag 0GWJ, remark-internal-hom-monoidal,
items (1) and (5) (blueprint: lem-trf-closed-evaluation-naturality).

The specified bifunctor `H` and its natural Hom bijections are retained as a
parametrized adjunction for tensoring on the right. Thus evaluation has exactly
Stacks' orientation `H(V,W) ⊗ V ⟶ W`, with no change of chosen internal Hom.

## Main definitions

- `closedRightEvaluation`: the specified counit.
- `closedIteratedEvaluationUncurried`: swap, then apply the two counits.
- `closedIteratedEvaluation`: its transpose.

## Main statement

- `closed_evaluation_naturality`: uniqueness, left uncurrying, and three-variable naturality.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open MonoidalCategory Opposite

/-- The counit `H(V,W) ⊗ V ⟶ W` of the given right-tensor adjunction.
Source: Stacks Project, categories.tex, Tag 0GWJ, item (1)
(blueprint: lem-trf-closed-evaluation-naturality). -/
def closedRightEvaluation {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {H : Cᵒᵖ ⥤ C ⥤ C} (adj : (curriedTensor C).flip ⊣₂ H) (V W : C) :
    (H.obj (op V)).obj W ⊗ V ⟶ W :=
  (adj.adj V).counit.app W

/-- The two-counit composite `(H(L,M) ⊗ K) ⊗ H(K,L) ⟶ M`.
Source: Stacks Project, categories.tex, Tag 0GWJ, construction of item (5)
(blueprint: lem-trf-closed-evaluation-naturality).
The associators exhibit exactly the swap of the last two factors. -/
def closedIteratedEvaluationUncurried
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    {H : Cᵒᵖ ⥤ C ⥤ C} (adj : (curriedTensor C).flip ⊣₂ H) (K L M : C) :
    ((H.obj (op L)).obj M ⊗ K) ⊗ (H.obj (op K)).obj L ⟶ M :=
  (α_ ((H.obj (op L)).obj M) K ((H.obj (op K)).obj L)).hom ≫
    (H.obj (op L)).obj M ◁ (β_ K ((H.obj (op K)).obj L)).hom ≫
    (H.obj (op L)).obj M ◁ closedRightEvaluation adj K L ≫
    closedRightEvaluation adj L M

/-- The transpose `e_{K,L,M}` of the specified swap-then-two-counit composite.
Source: Stacks Project, categories.tex, Tag 0GWJ, item (5)
(blueprint: lem-trf-closed-evaluation-naturality).
This uses the given bijection itself, rather than choosing an arbitrary morphism. -/
def closedIteratedEvaluation
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    {H : Cᵒᵖ ⥤ C ⥤ C} (adj : (curriedTensor C).flip ⊣₂ H) (K L M : C) :
    (H.obj (op L)).obj M ⊗ K ⟶ (H.obj (op ((H.obj (op K)).obj L))).obj M :=
  (adj.adj ((H.obj (op K)).obj L)).homEquiv _ _
    (closedIteratedEvaluationUncurried adj K L M)

/-- The iterated evaluation is uniquely specified by its right uncurrying, has the
stated left uncurrying, and is natural covariantly in `K,M` and contravariantly in `L`.
Source: Stacks Project, categories.tex, Tag 0GWJ, item (5), with the explicit
naturality expansion in the DAG (blueprint: lem-trf-closed-evaluation-naturality).

Proof:
1. Naturality of the given Hom bijections in the source identifies inverse
   transposition of q with `(q tensor identity) followed by epsilon`. Naturality
   in the other two variables identifies evaluation after H(a,b) with evaluation
   after a, followed by b. Tensor bifunctoriality is def-sfb-monoidal-category.
2. The inverse-bijection identities give existence and uniqueness of the displayed
   transpose. To uncurry on the left, precompose its right uncurrying by the
   associator and the braiding of B with A tensor K. Expand this braiding using
   the hexagon; cancel the adjacent inverse associators and the two opposite
   braidings of B with K, using symmetry. The remaining map is the braiding
   of B with A, followed by the two evaluations, as displayed.
3. Set a=H(t,v) and h=H(u,t). Apply the evaluation law of Step 1 to (u,t)
   and (t,v). These give epsilon after h as t after epsilon with u inserted,
   and epsilon after a as v after epsilon with t inserted, respectively.
4. Uncurry both sides of naturality with B'=H(K',L') on the right. Braiding
   naturality moves h through the swap on the first side and u through the swap
   on the second. Apply the two evaluation equations of Step 3 and tensor
   bifunctoriality; associator naturality puts both composites on the same
   parenthesized source. Both are v after epsilon(L,M), with t inserted before
   it, preceded by epsilon(K',L') with u inserted before it. Injectivity of the
   Hom bijection gives the claimed equality. No morphism is assumed invertible. -/
theorem closed_evaluation_naturality
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    {H : Cᵒᵖ ⥤ C ⥤ C} (adj : (curriedTensor C).flip ⊣₂ H)
    (K K' L L' M M' : C) (u : K ⟶ K') (t : L' ⟶ L) (v : M ⟶ M') :
    (∀ q : (H.obj (op L)).obj M ⊗ K ⟶ (H.obj (op ((H.obj (op K)).obj L))).obj M,
      ((adj.adj ((H.obj (op K)).obj L)).homEquiv _ _).symm q =
        closedIteratedEvaluationUncurried adj K L M ↔
      q = closedIteratedEvaluation adj K L M) ∧
    ((α_ ((H.obj (op K)).obj L) ((H.obj (op L)).obj M) K).hom ≫
      (β_ ((H.obj (op K)).obj L) ((H.obj (op L)).obj M ⊗ K)).hom ≫
      ((adj.adj ((H.obj (op K)).obj L)).homEquiv _ _).symm
        (closedIteratedEvaluation adj K L M) =
      (β_ ((H.obj (op K)).obj L) ((H.obj (op L)).obj M)).hom ▷ K ≫
        (α_ ((H.obj (op L)).obj M) ((H.obj (op K)).obj L) K).hom ≫
        (H.obj (op L)).obj M ◁ closedRightEvaluation adj K L ≫
        closedRightEvaluation adj L M) ∧
    (closedIteratedEvaluation adj K L M ≫
      (H.map (((H.map u.op).app L' ≫ (H.obj (op K)).map t).op)).app M ≫
      (H.obj (op ((H.obj (op K')).obj L'))).map v =
      (((H.map t.op).app M ≫ (H.obj (op L')).map v) ⊗ₘ u) ≫
        closedIteratedEvaluation adj K' L' M') := by
  sorry

end CategoryTheory
