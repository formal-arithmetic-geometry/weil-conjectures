/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.Paper.ModuleCupGodementPairing

/-! # Functorial flasque tensor complexes

Source: Stacks Project, Tags 0FKR and 0FKU, Godement resolutions and cup products.
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

/-- Functorial flasque augmented complexes with a natural tensor chain pairing.
Source: Stacks Project, Tag 0FKR, Lemma 20.30.1 (0FKS), and Tag 0FKU,
the naive cup product constructed using the Godement resolution.
(blueprint: lem-sc-module-cup-godement-coefficient-complexes)
Proof: construct the augmented cosimplicial Godement resolution for each of
F, G, F tensor G, F1, G1 and F1 tensor G1. Its degree n object is the (n+1)-fold
iterate of the product of stalk skyscrapers; cofaces insert the germ unit and
codegeneracies insert stalk evaluation. Apply these iterates to phi, psi and
phi tensor psi. Naturality of the unit and evaluation proves that the resulting
maps commute with cofaces, hence with the alternating differential, and with
the degree-zero augmentations. Extend the alternating complexes by zero in
negative degrees. The extra stalk codegeneracy contracts the augmented stalk
complex, so the augmentations are quasi-isomorphisms. Restrictions of the
product of stalks forget coordinates and are surjective, hence every term is
flasque; the negative zero terms are flasque too. The coordinatewise tensor
pairings commute with the iterated coefficient maps. Form the Alexander--Whitney
chain pairing using front and back faces: the cosimplicial identities imply the
chain equation, and coefficient naturality of the faces implies u followed by
the target map equals tensorHom of the two input maps followed by u1. Its
degree-zero component restricts to the tensor of the two germ augmentations,
which gives both displayed section equations. This argument uses no injective
resolution, class map or cohomological cup product. Empty schemes use empty
products, and zero coefficients or zero maps use the same additive construction. -/
theorem moduleCup_godement_coefficient_complexes (X : Scheme.{v})
    [MonoidalPreadditive X.Modules] (F G F₁ G₁ : X.Modules) (φ : F ⟶ F₁) (ψ : G ⟶ G₁) :
    ∃ (K L M : CochainComplex X.Modules ℤ)
      (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶ K)
      (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶ L)
      (c : (CochainComplex.singleFunctor X.Modules 0).obj (F ⊗ G) ⟶ M),
      QuasiIso a ∧ QuasiIso b ∧ QuasiIso c ∧
      K.IsStrictlyGE 0 ∧ L.IsStrictlyGE 0 ∧ M.IsStrictlyGE 0 ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (K.X n))) ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (L.X n))) ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (M.X n))) ∧
      ∃ u : HomologicalComplex.tensorObj K L ⟶ M,
        (∀ (V : X.Opens)
          (x : Γ(((CochainComplex.singleFunctor X.Modules 0).obj F).X 0, V))
          (y : Γ(((CochainComplex.singleFunctor X.Modules 0).obj G).X 0, V)),
          (u.f 0).val.app (op V)
            ((HomologicalComplex.ιTensorObj K L 0 0 0 (by simp)).val.app (op V)
              (tmulSection ((a.f 0).val.app (op V) x) ((b.f 0).val.app (op V) y))) =
            (c.f 0).val.app (op V) (tmulSection x y)) ∧
    ∃ (K₁ L₁ M₁ : CochainComplex X.Modules ℤ)
      (a₁ : (CochainComplex.singleFunctor X.Modules 0).obj F₁ ⟶ K₁)
      (b₁ : (CochainComplex.singleFunctor X.Modules 0).obj G₁ ⟶ L₁)
      (c₁ : (CochainComplex.singleFunctor X.Modules 0).obj (F₁ ⊗ G₁) ⟶ M₁),
      QuasiIso a₁ ∧ QuasiIso b₁ ∧ QuasiIso c₁ ∧
      K₁.IsStrictlyGE 0 ∧ L₁.IsStrictlyGE 0 ∧ M₁.IsStrictlyGE 0 ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (K₁.X n))) ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (L₁.X n))) ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (M₁.X n))) ∧
      ∃ u₁ : HomologicalComplex.tensorObj K₁ L₁ ⟶ M₁,
        (∀ (V : X.Opens)
          (x : Γ(((CochainComplex.singleFunctor X.Modules 0).obj F₁).X 0, V))
          (y : Γ(((CochainComplex.singleFunctor X.Modules 0).obj G₁).X 0, V)),
          (u₁.f 0).val.app (op V)
            ((HomologicalComplex.ιTensorObj K₁ L₁ 0 0 0 (by simp)).val.app (op V)
              (tmulSection ((a₁.f 0).val.app (op V) x) ((b₁.f 0).val.app (op V) y))) =
            (c₁.f 0).val.app (op V) (tmulSection x y)) ∧
        ∃ (l : K ⟶ K₁) (r : L ⟶ L₁) (t : M ⟶ M₁),
          a ≫ l = (CochainComplex.singleFunctor X.Modules 0).map φ ≫ a₁ ∧
          b ≫ r = (CochainComplex.singleFunctor X.Modules 0).map ψ ≫ b₁ ∧
          c ≫ t = (CochainComplex.singleFunctor X.Modules 0).map
            (@id (F ⊗ G ⟶ F₁ ⊗ G₁) (φ ⊗ₘ ψ)) ≫ c₁ ∧
          u ≫ t = HomologicalComplex.tensorHom l r ≫ u₁ := by
  sorry

end AlgebraicGeometry.Scheme.Modules
