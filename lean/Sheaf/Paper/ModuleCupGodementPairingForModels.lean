/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.Paper.ModuleCupGodementCodegeneracies
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-! # Tensor pairing of concrete Godement models -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Tensor multiplication for models with the canonical Godement codegeneracies.
Source: Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16; the coordinatewise
construction is applied to sheaves of modules over the structure sheaf.
(blueprint: lem-sc-module-cup-godement-model-pairing-pairing)
Proof: over an open U, send sections s of T(F) and t of T(G) to the family
whose x-coordinate is s(x) tensor t(x), mapped to the stalk of F tensor G.
This is O(U)-bilinear and commutes with restrictions; sheafifying the presheaf
tensor gives a morphism beta(F,G): T(F) tensor T(G) to T(F tensor G).
Its composite with the tensor of the germ units is the germ unit on F tensor G.
Projection to each x and evaluation on stalk representatives prove that beta
commutes with monad multiplication: both composites evaluate the same two
germ representatives at x and then tensor their values. Starting with the
identity pairing on F tensor G, recursively apply beta to the previous
iterates and then apply T to the previous pairing. Induction using these
unit and multiplication identities shows that the degreewise pairings commute
with every unit insertion and multiplication insertion. Transport through the
term equalities in the model predicates. The prescribed codegeneracies are
needed here as well as the prescribed cofaces. Since cofaces and codegeneracies
generate the simplex category, the transported maps form the desired natural
transformation. The three augmentation equations identify their zero components
with the germ units. The unit identity for beta, together with cancellation of
the term and extension isomorphisms, gives the displayed morphism equality.
The tensor of the two single-object identifications is the single-object
identification of F tensor G in degree zero. Empty products and zero module
sheaves satisfy the same coordinate formulas. -/
theorem moduleCup_godement_pairing_for_models (X : Scheme.{u}) (F G : X.Modules)
    (A B C : CosimplicialObject X.Modules)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
      (((alternatingCofaceMapComplex X.Modules).obj A).extend
        ComplexShape.embeddingUpNat))
    (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶
      (((alternatingCofaceMapComplex X.Modules).obj B).extend
        ComplexShape.embeddingUpNat))
    (c : (CochainComplex.singleFunctor X.Modules 0).obj (F ⊗ G) ⟶
      (((alternatingCofaceMapComplex X.Modules).obj C).extend
        ComplexShape.embeddingUpNat))
    (hA : ModuleCupGodementModel X F A a)
    (hB : ModuleCupGodementModel X G B b)
    (hC : ModuleCupGodementModel X (F ⊗ G) C c)
    (sA : ModuleCupGodementCodegeneracies X F A)
    (sB : ModuleCupGodementCodegeneracies X G B)
    (sC : ModuleCupGodementCodegeneracies X (F ⊗ G) C) :
    ∃ μ : CategoryTheory.Monoidal.FunctorCategory.tensorObj
        (C := SimplexCategory) (D := X.Modules) A B ⟶ C,
      ((a.f 0) ⊗ₘ (b.f 0)) ≫
        ((((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
          ComplexShape.embeddingUpNat (i := 0) rfl).hom ⊗ₘ
          (((alternatingCofaceMapComplex X.Modules).obj B).extendXIso
          ComplexShape.embeddingUpNat (i := 0) rfl).hom) ≫ μ.app ⦋0⦌ ≫
          (((alternatingCofaceMapComplex X.Modules).obj C).extendXIso
          ComplexShape.embeddingUpNat (i := 0) rfl).inv = c.f 0 := by sorry

end
end AlgebraicGeometry.Scheme.Modules
