/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Naturality and shifts of a tensor arrow and its mate

Source: Stacks Project, Tag 0B56, equation-projection-formula-map, arbitrary-arrow
categorical expansion (blueprint: lem-weil-pbc-tensor-arrow-mate-naturality-shifts).
The naturality and shift calculations are the agent-written expansion in that DAG node.

## Main definitions and statements

* `CategoryTheory.TensorArrowMate.beta`: the tensor comparison followed by `c ⊗ 1`.
* `CategoryTheory.TensorArrowMate.alpha`: its adjunct for the specified adjunction.
* `CategoryTheory.TensorArrowMate.naturality_shifts`: the two shift equations and the
  two naturality equations for a commuting square of arrows.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.TensorArrowMate

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- The map `βᶜ_P = μ_{K,P} ≫ (c ⊗ 1)`.
Source: Stacks Tag 0B56, equation-projection-formula-map, arbitrary-arrow expansion
(blueprint: lem-weil-pbc-tensor-arrow-mate-naturality-shifts). -/
def beta (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) (L : C ⥤ D)
    (μ : TC ⋙ (Functor.whiskeringRight C C D).obj L ≅
      (L ⋙ TD) ⋙ (Functor.whiskeringLeft C D D).obj L)
    {K : C} {E : D} (c : L.obj K ⟶ E) (P : C) :
    L.obj ((TC.obj K).obj P) ⟶ (TD.obj E).obj (L.obj P) :=
  (μ.hom.app K).app P ≫ (TD.map c).app (L.obj P)

/-- The map `αᶜ_P = η_{K ⊗ P} ≫ R(βᶜ_P)`, using the specified adjunction's
hom equivalence, not a separately chosen mate.
Source: Stacks Tag 0B56, equation-projection-formula-map, arbitrary-arrow expansion
(blueprint: lem-weil-pbc-tensor-arrow-mate-naturality-shifts). -/
def alpha (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) (L : C ⥤ D) (R : D ⥤ C)
    (adj : L ⊣ R)
    (μ : TC ⋙ (Functor.whiskeringRight C C D).obj L ≅
      (L ⋙ TD) ⋙ (Functor.whiskeringLeft C D D).obj L)
    {K : C} {E : D} (c : L.obj K ⟶ E) (P : C) :
    (TC.obj K).obj P ⟶ R.obj ((TD.obj E).obj (L.obj P)) :=
  adj.homEquiv _ _ (beta TC TD L μ c P)

/-- Naturality under commuting squares and compatibility with every integer shift.
Source: Stacks Tag 0B56, equation-projection-formula-map, arbitrary-arrow categorical
expansion (blueprint: lem-weil-pbc-tensor-arrow-mate-naturality-shifts).

Proof plan (the seven steps of the node):
1. Set `θ_Q = c ⊗ 1_Q`. Bifunctoriality makes θ natural in Q, and
   `Adjunction.homEquiv_unit` identifies alpha with `η ≫ R(beta)`.
2. Bifunctoriality, `c ≫ b = L(a) ≫ c'`, and naturality of μ in both inputs give
   `beta(c,P) ≫ (b ⊗ L(p)) = L(a ⊗ p) ≫ beta(c',P')`.
3. Apply R to step 2 and use unit naturality at `a ⊗ p` for alpha's naturality.
4. Naturality of tensor shift comparisons in the fixed input, applied at c, and θ's
   naturality at l give `θ_{L(P[n])} ≫ h = b_shift ≫ θ_{LP}[n]`.
   Composite comparisons are those of `Functor.CommShift.comp`.
5. Compose step 4 with μ at P[n], use μ's assumed shift equation, and preserve
   composition under [n] to obtain beta's shift equation.
6. Put X = K ⊗ P, X' = K ⊗ P[n], s = t^K. Unit naturality at s and the unit's
   shift equation give `η_{X'} ≫ R(a_shift) ≫ r = s ≫ η_X[n]`.
7. Expand alpha at P[n], use step 5, naturality of r at beta, and step 6.
   Preservation of composition by [n] gives alpha's shift equation.
No exactness, associator, tensor unit, or invertibility of c or alpha is used. -/
theorem naturality_shifts
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D) (L : C ⥤ D) (R : D ⥤ C)
    (adj : L ⊣ R)
    (μ : TC ⋙ (Functor.whiskeringRight C C D).obj L ≅
      (L ⋙ TD) ⋙ (Functor.whiskeringLeft C D D).obj L)
    [HasShift C ℤ] [HasShift D ℤ] [L.CommShift ℤ] [R.CommShift ℤ]
    [∀ M : C, (TC.obj M).CommShift ℤ] [∀ M : D, (TD.obj M).CommShift ℤ]
    (hTC : ∀ (M N : C) (f : M ⟶ N), NatTrans.CommShift (TC.map f) ℤ)
    (hTD : ∀ (M N : D) (f : M ⟶ N), NatTrans.CommShift (TD.map f) ℤ)
    (hη : NatTrans.CommShift adj.unit ℤ)
    (hμ : ∀ K : C, NatTrans.CommShift (F₁ := TC.obj K ⋙ L)
      (F₂ := L ⋙ TD.obj (L.obj K)) (μ.hom.app K) ℤ) :
    (∀ (K : C) (E : D) (c : L.obj K ⟶ E) (P : C) (n : ℤ),
      beta TC TD L μ c (P⟦n⟧) ≫ ((L ⋙ TD.obj E).commShiftIso n).hom.app P =
        ((TC.obj K ⋙ L).commShiftIso n).hom.app P ≫
          (beta TC TD L μ c P)⟦n⟧' ∧
      alpha TC TD L R adj μ c (P⟦n⟧) ≫
          (((L ⋙ TD.obj E) ⋙ R).commShiftIso n).hom.app P =
        ((TC.obj K).commShiftIso n).hom.app P ≫
          (alpha TC TD L R adj μ c P)⟦n⟧') ∧
    (∀ (K K' : C) (E E' : D) (c : L.obj K ⟶ E) (c' : L.obj K' ⟶ E')
      (a : K ⟶ K') (b : E ⟶ E'), c ≫ b = L.map a ≫ c' →
      ∀ (P P' : C) (p : P ⟶ P'),
      beta TC TD L μ c P ≫
          ((TD.map b).app (L.obj P) ≫ (TD.obj E').map (L.map p)) =
        L.map ((TC.map a).app P ≫ (TC.obj K').map p) ≫ beta TC TD L μ c' P' ∧
      alpha TC TD L R adj μ c P ≫
          R.map ((TD.map b).app (L.obj P) ≫ (TD.obj E').map (L.map p)) =
        ((TC.map a).app P ≫ (TC.obj K').map p) ≫ alpha TC TD L R adj μ c' P') := by
  sorry

end CategoryTheory.TensorArrowMate
