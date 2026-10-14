/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.ModuleCupGodementCodegeneracies
public import Sheaf.Paper.ModuleCupAWComponents

/-! # Godement f-maps compatible with front/back tensor summands

Source: Stacks Project, Tags 0FKR and 0FKU, extended coordinatewise to a scheme morphism.
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

/-- Concrete Godement models admit compatible coefficient f-maps on their front/back summands.
This supplies no quasi-isomorphisms, flasqueness, or tensor cochain maps.
Source: Stacks Project, Tag 0FKR, the product-of-stalks construction; Tag 0FKU,
the naive product; Banerjee, arXiv:1004.1491, §1.1.4, front/back formula.
(blueprint: lem-sc-module-cup-godement-fmap-summands)
Proof: use the term identifications of the given six models to work with the
iterated products of stalk skyscrapers. Their cofaces insert germs and their
prescribed codegeneracies evaluate stalk coordinates.
For a coefficient map H → f_*H', send a family on V to the family on f⁻¹V
whose x' coordinate is the image of its f(x') coordinate under the induced
semilinear map H_{f(x')} → H'_{x'}. This map sends a germ represented on V to
the germ at x' of its coefficient-map image on f⁻¹V. This is linear over O_X(V)
through the structure-sheaf morphism. Restriction forgets the same coordinates
in both orders. The coordinate formula
commutes with germ insertion: both sides take the image of the same germ.
It commutes with evaluation because evaluation of the induced family at x'
is the coefficient stalk image of evaluation at f(x'). Iterate these identities
at every position, giving maps commuting with all cofaces and codegeneracies.
Take their alternating coface complexes and extend by zero, using zero maps
in negative degrees. Additivity of pushforward gives the three displayed chain
maps. Apply this construction to φ, ψ and χ. The germ identity gives their
three augmentation squares.
Choose the pairings from the same coordinatewise Godement tensor construction
on both schemes. The degree-zero unit identity gives the two ZeroPair equations.
At x', the image of a tensor of coordinates is the tensor of their images,
by hχ, applied on representatives of the two germs on a common open
neighbourhood of f(x'). Induction propagates this equality through every Godement
iterate. The iterated f-maps commute with the front and back simplex inclusions,
so conjugating by the extension identifications gives the stated awSummand
identity in every nonnegative bidegree. There is no totalization here: it is
an equality of the individual front/back section operations. Empty schemes
use empty products, zero coefficients use zero families, and bidegree (0,0)
uses identity front/back faces; no flatness hypothesis is used. -/
theorem moduleCup_godement_fmap_summands (X X' : Scheme.{v}) (f : X' ⟶ X)
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
        (μ₁ : moduleCup_cosimplicialTensor X' A₁ B₁ ⟶ C₁),
        (∀ (V : X.Opens)
          (x : Γ(((CochainComplex.singleFunctor X.Modules 0).obj F).X 0, V))
          (y : Γ(((CochainComplex.singleFunctor X.Modules 0).obj G).X 0, V)),
          (moduleCup_cosimplicialZeroPair X A B C μ).val.app (op V)
            (tmulSection ((a.f 0).val.app (op V) x) ((b.f 0).val.app (op V) y)) =
              (c.f 0).val.app (op V) (tmulSection x y)) ∧
        (∀ (V : X'.Opens)
          (x : Γ(((CochainComplex.singleFunctor X'.Modules 0).obj
            F₁).X 0, V))
          (y : Γ(((CochainComplex.singleFunctor X'.Modules 0).obj
            G₁).X 0, V)),
          (moduleCup_cosimplicialZeroPair X' A₁ B₁ C₁ μ₁).val.app (op V)
            (tmulSection ((a₁.f 0).val.app (op V) x) ((b₁.f 0).val.app (op V) y)) =
              (c₁.f 0).val.app (op V) (tmulSection x y)) ∧
        ∃ (l : moduleCup_cosimplicialComplex X A ⟶
            ((pushforward f).mapHomologicalComplex (.up ℤ)).obj
              (moduleCup_cosimplicialComplex X' A₁))
          (r : moduleCup_cosimplicialComplex X B ⟶
            ((pushforward f).mapHomologicalComplex (.up ℤ)).obj
              (moduleCup_cosimplicialComplex X' B₁))
          (t : moduleCup_cosimplicialComplex X C ⟶
            ((pushforward f).mapHomologicalComplex (.up ℤ)).obj
              (moduleCup_cosimplicialComplex X' C₁)),
          a.f 0 ≫ l.f 0 = φ ≫ (pushforward f).map (a₁.f 0) ∧
          b.f 0 ≫ r.f 0 = ψ ≫ (pushforward f).map (b₁.f 0) ∧
          c.f 0 ≫ t.f 0 = χ ≫ (pushforward f).map (c₁.f 0) ∧
          ∀ (p q : ℕ) (V : X.Opens)
            (x : Γ((moduleCup_cosimplicialComplex X A).X (p : ℤ), V))
            (y : Γ((moduleCup_cosimplicialComplex X B).X (q : ℤ), V)),
            (t.f ((p + q : ℕ) : ℤ)).val.app (op V)
              ((moduleCup_awSummand X A B C μ (p : ℤ) (q : ℤ)
                ((p + q : ℕ) : ℤ) (by simp)).val.app (op V) (tmulSection x y)) =
            (moduleCup_awSummand X' A₁ B₁ C₁ μ₁ (p : ℤ) (q : ℤ)
              ((p + q : ℕ) : ℤ) (by simp)).val.app (op (f ⁻¹ᵁ V))
                (tmulSection ((l.f (p : ℤ)).val.app (op V) x)
                  ((r.f (q : ℤ)).val.app (op V) y)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
