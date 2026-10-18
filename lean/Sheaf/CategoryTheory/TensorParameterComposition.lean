/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Tensor-parameter composition through an adjunction

Source: Stacks Project, Categories, Tag 0037, the counit formula for adjunction;
the explicit tensor-parameter calculation in the DAG, serving paragraph 2 of the blueprint
proof of `prop-coef-integral-exceptional-adjoint`
(blueprint: lem-coef-monoidal-adjunction-parameter-composition).

The tensor products here are arbitrary bifunctors, with no monoidal coherence assumptions.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open CategoryTheory.Prod

/-- The canonical map `S ⊗ G N → G (F S ⊗ N)`, defined by transposing the tensor of
`1` with the counit after the inverse tensor comparison. Its transpose is the specified
map, uniquely, by the inverse laws of `Adjunction.homEquiv`.
Source: Stacks Project, Tag 0037, counit description of the adjunction bijection;
the definition of lambda in the DAG
(blueprint: lem-coef-monoidal-adjunction-parameter-composition). -/
def tensorParameterMate {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    (tensorC : C × C ⥤ C) (tensorD : D × D ⥤ D)
    {F : C ⥤ D} {G : D ⥤ C}
    (μ : F.prod F ⋙ tensorD ≅ tensorC ⋙ F) (adj : F ⊣ G) (S : C) (N : D) :
    tensorC.obj (S, G.obj N) ⟶ G.obj (tensorD.obj (F.obj S, N)) :=
  adj.homEquiv _ _
    (μ.inv.app (S, G.obj N) ≫ tensorD.map (𝟙 (F.obj S) ×ₘ adj.counit.app N))

/-- Tensor-parameter composition is preserved by the specified adjunction, with Phi given by
`adj.homEquiv.symm` and f-sharp given by the tensor comparison followed by `F.map f` and
the counit. The parenthesization of the three tensor factors is fixed throughout.
Source: Stacks Project, Tag 0037, and the explicit three-step DAG calculation
(blueprint: lem-coef-monoidal-adjunction-parameter-composition).

Proof: Put A = T tensor P, B = F S tensor N and q = 1 tensor f. Expand Phi as
`F.map` followed by the counit, using `lem-weil-pbc-adjunction-of-natural-bijection`.
Functoriality of F and naturality of the counit at g identify Phi of G(g) after lambda
and q with Phi(lambda) after F(q), followed by g. Replace Phi(lambda) by its defining
inverse-comparison/counit composite. Naturality of mu at (1, f), together with F(1) = 1,
cancels the inverse comparison against mu at (S, A). The category laws of
`def-nagata-category` then leave g after (1 tensor counit) after (1 tensor F(f)).
Precompose with 1 tensor mu at (T, P). Functoriality of tensorD combines the three
maps in the second tensor factor into f-sharp, giving the right side. No associator,
unitor, closed structure, dual, or inverse of lambda is used. -/
theorem tensorParameterComposition {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    (tensorC : C × C ⥤ C) (tensorD : D × D ⥤ D)
    {F : C ⥤ D} {G : D ⥤ C}
    (μ : F.prod F ⋙ tensorD ≅ tensorC ⋙ F) (adj : F ⊣ G)
    (S T P : C) (N N' : D)
    (f : tensorC.obj (T, P) ⟶ G.obj N) (g : tensorD.obj (F.obj S, N) ⟶ N') :
    tensorD.map (𝟙 (F.obj S) ×ₘ μ.hom.app (T, P)) ≫
        μ.hom.app (S, tensorC.obj (T, P)) ≫
        (adj.homEquiv (tensorC.obj (S, tensorC.obj (T, P))) N').symm
          (tensorC.map (𝟙 S ×ₘ f) ≫ tensorParameterMate tensorC tensorD μ adj S N ≫
            G.map g) =
      tensorD.map (𝟙 (F.obj S) ×ₘ
        (μ.hom.app (T, P) ≫ F.map f ≫ adj.counit.app N)) ≫ g := by
  rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm,
    tensorParameterMate, Equiv.symm_apply_apply]
  have hμ : tensorD.map (𝟙 (F.obj S) ×ₘ F.map f) ≫ μ.hom.app (S, G.obj N) =
      μ.hom.app (S, tensorC.obj (T, P)) ≫ F.map (tensorC.map (𝟙 S ×ₘ f)) := by
    simpa using μ.hom.naturality (𝟙 S ×ₘ f)
  simp only [Category.assoc]
  rw [← Category.assoc (μ.hom.app (S, tensorC.obj (T, P))), ← hμ]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← tensorD.map_comp_assoc, ← tensorD.map_comp_assoc]
  simp

end CategoryTheory
