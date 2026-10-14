/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor

/-! # Flasque tensor complexes across a scheme morphism

Source: Stacks Project, Tags 0FKS and 0FKU, the functorial Godement construction.
(blueprint: lem-sc-module-cup-pullback-flasque-complexes).
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Integer flasque resolutions and tensor chain pairings admit simultaneous f-maps.
This assertion concerns complexes and sections only, with no injective comparisons
or cohomology-class maps.
Source: Stacks Project, Tag 0FKS, cohomology-lemma-godement-resolution; Tag 0FKU,
section-cup-product, naive products and Lemma 20.31.3.
(blueprint: lem-sc-module-cup-pullback-flasque-complexes).

Proof: form the six augmented cosimplicial Godement models. For a coefficient
f-map H → f_*H', the coordinate of a product-of-stalks section at x' is obtained
from its coordinate at f(x') by the induced semilinear stalk map. This is linear
when the target is viewed by pushforward and commutes with restrictions. The
coordinate maps commute with germ insertion and stalk evaluation: both composites
apply the coefficient stalk map to the same germ, respectively the same evaluated
coordinate. Iterate to obtain maps commuting with every coface and codegeneracy.
Apply the alternating coface functor and extend by zero in negative degrees.
The augmented stalk complexes contract by evaluation, so the augmentations are
quasi-isomorphisms. Restriction of a product of skyscrapers forgets coordinates,
so each term is flasque; negative terms are zero and flasque.
Use coordinatewise tensoring followed by the front/back Alexander--Whitney faces
to define u and u₁. The cosimplicial identities give the signed chain equation.
At degree zero the faces are identities and the germ tensor equation gives the
two augmentation formulas. Apply the three f-maps induced by the adjunction units,
composing the tensor coefficient map with the section-normalized pullback tensor
comparison. That normalization gives tensor-of-images on every stalk coordinate.
Commutation with the front/back faces then gives the displayed equality on every
open V and in every nonnegative bidegree. The three degree-zero squares are the
germ naturality equations. The construction works for the empty scheme (empty
products), zero coefficients, and degree zero, without coefficient flatness. -/
theorem moduleCup_pullback_flasque_complexes (X X' : Scheme.{v}) (f : X' ⟶ X)
    [MonoidalPreadditive X.Modules] [MonoidalPreadditive X'.Modules] (F G : X.Modules) :
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
    ∃ (K₁ L₁ M₁ : CochainComplex X'.Modules ℤ)
      (a₁ : (CochainComplex.singleFunctor X'.Modules 0).obj ((tensorPullback f).obj F) ⟶ K₁)
      (b₁ : (CochainComplex.singleFunctor X'.Modules 0).obj ((tensorPullback f).obj G) ⟶ L₁)
      (c₁ : (CochainComplex.singleFunctor X'.Modules 0).obj
        ((tensorPullback f).obj F ⊗ (tensorPullback f).obj G) ⟶ M₁),
      QuasiIso a₁ ∧ QuasiIso b₁ ∧ QuasiIso c₁ ∧
      K₁.IsStrictlyGE 0 ∧ L₁.IsStrictlyGE 0 ∧ M₁.IsStrictlyGE 0 ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X'.toRingedSpace)).obj (K₁.X n))) ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X'.toRingedSpace)).obj (L₁.X n))) ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X'.toRingedSpace)).obj (M₁.X n))) ∧
      ∃ u₁ : HomologicalComplex.tensorObj K₁ L₁ ⟶ M₁,
        (∀ (V : X'.Opens)
          (x : Γ(((CochainComplex.singleFunctor X'.Modules 0).obj
            ((tensorPullback f).obj F)).X 0, V))
          (y : Γ(((CochainComplex.singleFunctor X'.Modules 0).obj
            ((tensorPullback f).obj G)).X 0, V)),
          (u₁.f 0).val.app (op V)
            ((HomologicalComplex.ιTensorObj K₁ L₁ 0 0 0 (by simp)).val.app (op V)
              (tmulSection ((a₁.f 0).val.app (op V) x) ((b₁.f 0).val.app (op V) y))) =
            (c₁.f 0).val.app (op V) (tmulSection x y)) ∧
        ∃ (l : K ⟶ ((pushforward f).mapHomologicalComplex (.up ℤ)).obj K₁)
          (r : L ⟶ ((pushforward f).mapHomologicalComplex (.up ℤ)).obj L₁)
          (t : M ⟶ ((pushforward f).mapHomologicalComplex (.up ℤ)).obj M₁),
          a.f 0 ≫ l.f 0 =
            (Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F ≫
              (pushforward f).map (a₁.f 0) ∧
          b.f 0 ≫ r.f 0 =
            (Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G ≫
              (pushforward f).map (b₁.f 0) ∧
          c.f 0 ≫ t.f 0 =
            (Classical.choose (exists_tensorPullbackAdjunction f)).unit.app (F ⊗ G) ≫
              (pushforward f).map ((Classical.choose (module_pullback_tensor f) F G).hom) ≫
              (pushforward f).map (c₁.f 0) ∧
          ∀ (p q : ℕ) (V : X.Opens)
            (x : Γ(K.X (p : ℤ), V)) (y : Γ(L.X (q : ℤ), V)),
            (t.f ((p + q : ℕ) : ℤ)).val.app (op V)
              ((u.f _).val.app (op V)
                ((HomologicalComplex.ιTensorObj K L (p : ℤ) (q : ℤ)
                  ((p + q : ℕ) : ℤ) (by simp)).val.app (op V) (tmulSection x y))) =
            (u₁.f _).val.app (op (f ⁻¹ᵁ V))
              ((HomologicalComplex.ιTensorObj K₁ L₁ (p : ℤ) (q : ℤ)
                ((p + q : ℕ) : ℤ) (by simp)).val.app (op (f ⁻¹ᵁ V))
                  (tmulSection ((l.f (p : ℤ)).val.app (op V) x)
                    ((r.f (q : ℤ)).val.app (op V) y))) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
