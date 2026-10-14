/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.ModuleCupResolutionFMap
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor

/-! # Pullback of augmented computing pairings

Source: Stacks Project, Tags 0FKS and 0FKU, functorial Godement resolutions
and the Alexander--Whitney tensor pairing.
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

/-- Pullback admits simultaneous sheaf cochain maps of computing pairings over the
three coefficient f-maps, preserving the pairing before passing to cohomology.
Source: Stacks Project, Tag 0FKS, cohomology-lemma-godement-resolution;
Tag 0FKU, section-cup-product, naive products and Lemma 20.31.3.
(blueprint: lem-sc-module-cup-pullback-augmented-pairings).

Proof: take the concrete cosimplicial Godement models on X and X' for the three
coefficients. On an open V, send the coordinate indexed by f(x') through the
stalk map of the coefficient f-map to the coordinate indexed by x' over f-inverse V.
The germ unit commutes with these maps since both sides take the germ of the
image section. Stalk evaluation commutes since both sides evaluate that same
coordinate. Iteration therefore commutes with cofaces and codegeneracies and
gives maps of the augmented alternating complexes into the termwise pushforward.
For the tensor coefficient compose with the Godement map induced by the canonical
tensor-pullback comparison. Its normalization on section tensors and coordinatewise
tensoring imply compatibility with the Godement tensor pairing. The front and back
faces defining Alexander--Whitney commute with these maps, so the pairing equation
holds in every bidegree. Restrict to natural indices. Godement terms are flasque,
and their augmented stalk complexes contract by evaluation. Choose injective
comparisons over the three augmentations on each scheme; flasque acyclicity and
acyclic resolution comparison show that these compute cohomology. This constructs
D and E without imposing any cohomology-class equations. The augmentation equations
are the degree-zero germ equations. Taking sections and restricting along the
canonical equality f-inverse(top)=top gives the stated strict equation.
Empty schemes have empty stalk products, zero coefficients give zero products,
and degree zero uses the ordinary germ tensor equation. No exactness of tensor
pullback or flatness of the coefficients is required. -/
theorem moduleCup_pullback_augmented_pairings (X X' : Scheme.{v}) (f : X' ⟶ X)
    (F G : X.Modules) :
    ∃ (D : CupResolutionPairing F G)
      (E : CupResolutionPairing ((tensorPullback f).obj F) ((tensorPullback f).obj G))
      (l : D.left.K ⟶
        ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj E.left.K)
      (r : D.right.K ⟶
        ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj E.right.K)
      (t : D.target.K ⟶
        ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj E.target.K),
      (D.left.augmentation.f 0 ≫ l.f 0 =
        (Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F ≫
          (pushforward f).map (E.left.augmentation.f 0)) ∧
      (D.right.augmentation.f 0 ≫ r.f 0 =
        (Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G ≫
          (pushforward f).map (E.right.augmentation.f 0)) ∧
      (D.target.augmentation.f 0 ≫ t.f 0 =
        (Classical.choose (exists_tensorPullbackAdjunction f)).unit.app (F ⊗ G) ≫
          (pushforward f).map ((Classical.choose (module_pullback_tensor f) F G).hom) ≫
          (pushforward f).map (E.target.augmentation.f 0)) ∧
      (∀ (p q : ℕ) (a : Γ(D.left.K.X p, ⊤)) (b : Γ(D.right.K.X q, ⊤)),
        (cupResolutionGlobalMap f t).f (p + q) (D.pair p q ⊤ a b) =
          E.pair p q ⊤ ((cupResolutionGlobalMap f l).f p a)
            ((cupResolutionGlobalMap f r).f q b)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
