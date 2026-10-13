/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.ModuleCupResolutionData
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Cosimplicial input for the Godement cup product -/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section


/-- Extend the unnormalized alternating coface complex by zero in negative degrees.
Source: Stacks Project, Tag 0FKR (blueprint: lem-sc-module-cup-godement-cosimplicial-input). -/
def moduleCup_cosimplicialComplex (X : Scheme.{u}) (A : CosimplicialObject X.Modules) :
    CochainComplex X.Modules ℤ :=
  ((alternatingCofaceMapComplex X.Modules).obj A).extend ComplexShape.embeddingUpNat

/-- The degree-zero identification with the cosimplicial term.
Source: Stacks Project, Tag 0FKR (blueprint: lem-sc-module-cup-godement-cosimplicial-input). -/
def moduleCup_cosimplicialZeroIso (X : Scheme.{u}) (A : CosimplicialObject X.Modules) :
    (moduleCup_cosimplicialComplex X A).X 0 ≅ A.obj ⦋0⦌ :=
  ((alternatingCofaceMapComplex X.Modules).obj A).extendXIso
    ComplexShape.embeddingUpNat (i := 0) rfl

/-- Pointwise tensor product of two cosimplicial objects.
Source: Stacks Project, Tag 0FKR
(blueprint: lem-sc-module-cup-godement-cosimplicial-input). -/
def moduleCup_cosimplicialTensor (X : Scheme.{u})
    (A B : CosimplicialObject X.Modules) : CosimplicialObject X.Modules :=
  CategoryTheory.Monoidal.FunctorCategory.tensorObj
    (C := SimplexCategory) (D := X.Modules) A B

/-- The degree-zero pairing induced by a pointwise cosimplicial tensor morphism.
Source: Stacks Project, Tag 0FKR (blueprint: lem-sc-module-cup-godement-cosimplicial-input). -/
def moduleCup_cosimplicialZeroPair (X : Scheme.{u})
    (A B C : CosimplicialObject X.Modules) (μ : moduleCup_cosimplicialTensor X A B ⟶ C) :
    (moduleCup_cosimplicialComplex X A).X 0 ⊗
      (moduleCup_cosimplicialComplex X B).X 0 ⟶ (moduleCup_cosimplicialComplex X C).X 0 :=
  ((moduleCup_cosimplicialZeroIso X A).hom ⊗ₘ
    (moduleCup_cosimplicialZeroIso X B).hom) ≫ μ.app ⦋0⦌ ≫
    (moduleCup_cosimplicialZeroIso X C).inv

/-- Flasque Godement resolutions with a pointwise cosimplicial multiplication.
Source: Stacks Project, Cohomology of Sheaves, Section 20.30, Tag 0FKR,
Lemma 20.30.1 (Tag 0FKS); Banerjee, Tensor Structure on Smooth Motives,
arXiv:1004.1491, §1.1.4, pp. 15--16 (cosimplicial Godement multiplication).
(blueprint: lem-sc-module-cup-godement-cosimplicial-input)
Proof: let T(F) be the sheaf of all discontinuous sections of the stalks of F.
It has sections over V equal to the product of F_x for x in V, with the O(V)
action through germs. The germ map is the unit of the stalk/product-skyscraper
adjunction. Iterate its monad: the n-th cosimplicial term is T^(n+1)(F), faces
insert the unit, and degeneracies use the counit on stalks. Take its alternating
coface complex and extend by zero. Evaluation at a fixed stalk supplies an extra
codegeneracy of the augmented object, so its stalk complex is contractible;
exactness and conservativity of stalks imply that the augmentation is a quasi-isomorphism.
Every nonnegative term is a product-of-stalks sheaf; its restrictions are projections
and are surjective. Negative terms are zero and therefore flasque. Coordinatewise
tensor products give T(F) tensor T(G) → T(F tensor G); iterate them to obtain a
cosimplicial morphism μ. The unit and counit commute with this multiplication,
which proves compatibility with faces, degeneracies, and the degree-zero germ maps.
For an empty scheme every coordinate product and every stalk assertion is empty;
zero sheaves give the same construction without any nonvanishing assumption.
This statement supplies only a pointwise cosimplicial multiplication, not a map
of total tensor complexes; the Alexander--Whitney construction is separate. -/
theorem moduleCup_godement_cosimplicial_input (X : Scheme.{u}) (F G : X.Modules) :
    ∃ (A B C : CosimplicialObject X.Modules)
      (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
        moduleCup_cosimplicialComplex X A)
      (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶
        moduleCup_cosimplicialComplex X B)
      (c : (CochainComplex.singleFunctor X.Modules 0).obj (F ⊗ G) ⟶
        moduleCup_cosimplicialComplex X C)
      (μ : moduleCup_cosimplicialTensor X A B ⟶ C),
      QuasiIso a ∧ QuasiIso b ∧ QuasiIso c ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
          ((moduleCup_cosimplicialComplex X A).X n))) ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
          ((moduleCup_cosimplicialComplex X B).X n))) ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
          ((moduleCup_cosimplicialComplex X C).X n))) ∧
      ∀ (V : X.Opens)
        (x : Γ(((CochainComplex.singleFunctor X.Modules 0).obj F).X 0, V))
        (y : Γ(((CochainComplex.singleFunctor X.Modules 0).obj G).X 0, V)),
        (moduleCup_cosimplicialZeroPair X A B C μ).val.app (op V)
          (tmulSection ((a.f 0).val.app (op V) x) ((b.f 0).val.app (op V) y)) =
        (c.f 0).val.app (op V) (tmulSection x y) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
