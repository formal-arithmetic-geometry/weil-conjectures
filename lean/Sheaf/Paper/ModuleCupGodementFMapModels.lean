/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.Paper.ModuleCupGodementCodegeneracies
public import Sheaf.Paper.ModuleCupGodementCosimplicialInput

/-! # Augmented cosimplicial Godement maps across a scheme morphism

The remaining construction takes place entirely before alternating cofaces and extension by zero.
Source: Stacks Project, Tags 0FKR and 0FKU, extended by the coordinate argument below.
(blueprint: new-module-cup-godement-fmap-models).
-/

@[expose] public section
universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Compatible augmented cosimplicial Godement f-maps and tensor pairings.
Source: Stacks Project, Tags 0FKR and 0FKU; Banerjee, arXiv:1004.1491, §1.1.4.
(blueprint: new-module-cup-godement-fmap-models)
Proof: For H → f_*H', map a stalk germ represented by s on V to the germ of its
coefficient image on f⁻¹V at x'. This defines the semilinear stalk map at x'
from the stalk at f(x'); common refinements prove independence of representatives.
The x' coordinate of the induced product-of-stalks map is the image of the
f(x') coordinate. Module linearity follows through the structure-sheaf map;
restriction forgets the same coordinates in both orders. Projection to each x'
proves compatibility with the germ unit and evaluation multiplication. Iterate
these maps and these two identities to commute with every coface and prescribed
codegeneracy. Transport through the model term equalities; equality of their
proof witnesses identifies the term equalities used for cofaces and codegeneracies.
Since these generate the simplex category, this gives the three natural
transformations. The unit identity and the model augmentation identities give
the three displayed degree-zero equations.
Choose on each scheme the coordinatewise tensor map beta of stalk skyscraper
products. Starting with p₀ = identity, define pₙ₊₁ = beta followed by T(pₙ).
The unit and multiplication laws make p commute with all insertions and collapses,
so model transport gives the two cosimplicial pairings. The unit law gives their
augmentation equations. To check the pairing square, represent the two stalk
germs on a common neighbourhood of f(x'). The hypothesis hχ on this neighbourhood
says their stalk images tensor correctly. Projection to x' proves the one-step
beta square; induction propagates it to pₙ, hence to each cosimplicial degree.
Empty products, zero sheaves and degree zero obey the same formulas. This lemma
asserts no extended-complex maps or Alexander--Whitney summand identities. -/
theorem moduleCup_godement_fmap_models (X X' : Scheme.{v}) (f : X' ⟶ X)
    [MonoidalPreadditive X.Modules] [MonoidalPreadditive X'.Modules]
    (F G : X.Modules) (F₁ G₁ : X'.Modules)
    (φ : F ⟶ (pushforward f).obj F₁) (ψ : G ⟶ (pushforward f).obj G₁)
    (χ : F ⊗ G ⟶ (pushforward f).obj (F₁ ⊗ G₁))
    (hχ : ∀ (V : X.Opens) (x : Γ(F, V)) (y : Γ(G, V)),
      χ.val.app (op V) (tmulSection x y) =
        tmulSection (φ.val.app (op V) x) (ψ.val.app (op V) y))
    (A B C : CosimplicialObject X.Modules)
      (A₁ B₁ C₁ : CosimplicialObject X'.Modules)
      (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
        moduleCup_cosimplicialComplex X A)
      (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶
        moduleCup_cosimplicialComplex X B)
      (c : (CochainComplex.singleFunctor X.Modules 0).obj (F ⊗ G) ⟶
        moduleCup_cosimplicialComplex X C)
      (a₁ : (CochainComplex.singleFunctor X'.Modules 0).obj F₁ ⟶
        moduleCup_cosimplicialComplex X' A₁)
      (b₁ : (CochainComplex.singleFunctor X'.Modules 0).obj G₁ ⟶
        moduleCup_cosimplicialComplex X' B₁)
      (c₁ : (CochainComplex.singleFunctor X'.Modules 0).obj
        (F₁ ⊗ G₁) ⟶
        moduleCup_cosimplicialComplex X' C₁)
    (hA : ModuleCupGodementModel X F A a) (hB : ModuleCupGodementModel X G B b)
    (hC : ModuleCupGodementModel X (F ⊗ G) C c)
    (hA₁ : ModuleCupGodementModel X' F₁ A₁ a₁)
    (hB₁ : ModuleCupGodementModel X' G₁ B₁ b₁)
    (hC₁ : ModuleCupGodementModel X'
      (F₁ ⊗ G₁) C₁ c₁)
    (sA : ModuleCupGodementCodegeneracies X F A)
    (sB : ModuleCupGodementCodegeneracies X G B)
    (sC : ModuleCupGodementCodegeneracies X (F ⊗ G) C)
    (sA₁ : ModuleCupGodementCodegeneracies X' F₁ A₁)
    (sB₁ : ModuleCupGodementCodegeneracies X' G₁ B₁)
    (sC₁ : ModuleCupGodementCodegeneracies X'
      (F₁ ⊗ G₁) C₁) :
    ∃ (μ : moduleCup_cosimplicialTensor X A B ⟶ C)
      (μ₁ : moduleCup_cosimplicialTensor X' A₁ B₁ ⟶ C₁)
      (g : A ⟶ A₁ ⋙ pushforward f) (h : B ⟶ B₁ ⋙ pushforward f)
      (k : C ⟶ C₁ ⋙ pushforward f),
      ((a.f 0) ⊗ₘ (b.f 0)) ≫ moduleCup_cosimplicialZeroPair X A B C μ = c.f 0 ∧
      ((a₁.f 0) ⊗ₘ (b₁.f 0)) ≫ moduleCup_cosimplicialZeroPair X' A₁ B₁ C₁ μ₁ =
        c₁.f 0 ∧
      a.f 0 ≫ (moduleCup_cosimplicialZeroIso X A).hom ≫ g.app ⦋0⦌ =
        φ ≫ (pushforward f).map (a₁.f 0 ≫ (moduleCup_cosimplicialZeroIso X' A₁).hom) ∧
      b.f 0 ≫ (moduleCup_cosimplicialZeroIso X B).hom ≫ h.app ⦋0⦌ =
        ψ ≫ (pushforward f).map (b₁.f 0 ≫ (moduleCup_cosimplicialZeroIso X' B₁).hom) ∧
      c.f 0 ≫ (moduleCup_cosimplicialZeroIso X C).hom ≫ k.app ⦋0⦌ =
        χ ≫ (pushforward f).map (c₁.f 0 ≫ (moduleCup_cosimplicialZeroIso X' C₁).hom) ∧
      ∀ (n : SimplexCategory) (V : X.Opens)
        (x : Γ(A.obj n, V)) (y : Γ(B.obj n, V)),
        (k.app n).val.app (op V) ((μ.app n).val.app (op V) (tmulSection x y)) =
          (μ₁.app n).val.app (op (f ⁻¹ᵁ V))
            (tmulSection ((g.app n).val.app (op V) x) ((h.app n).val.app (op V) y)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
