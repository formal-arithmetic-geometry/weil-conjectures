/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal

/-!
# The derived category of a braided (symmetric) category is braided (symmetric)

Let `C` be an abelian monoidal category satisfying the hypotheses under which the derived
category `D(C)` is monoidal for the derived tensor product, i.e. those of
`WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`: the derived tensor
product is the binary left derived functor of the tensor product on
`K(C) := HomotopyCategory C (ComplexShape.up ℤ)`. This file states that if moreover `C` is
braided, respectively symmetric, then so is `D(C)`.

The only new mathematical input is the braiding on `C`: no further K-flat hypothesis is
needed, the derived monoidal structure being taken as a hypothesis here
(`DerivedCategory.Qh.HasDerivedMonoidalCategory _`). In practice that hypothesis, together
with the `GradedObject` hypotheses below, is what `C` Grothendieck abelian, monoidal
preadditive and monoidal closed with functorial flat resolutions provides; none of those is
needed for the transport of the braiding itself, so they are not assumed.

The proofs are left as `sorry`. Following the roadmap, they are to be obtained from the
chain `C braided ⟹ CochainComplex C ℤ braided ⟹ K(C) braided ⟹ D(C) braided`:

1. **The Koszul braiding on complexes (the step carrying the sign content).** The braiding of
   `C` cannot be transported degreewise: on the summand `X p ⊗ Y q` of the tensor product of
   complexes the correct map is `(-1) ^ (p * q) • β_ (X p) (Y q)`, the Koszul sign being what
   makes the flip commute with the total differential. This should be *assembled*, not
   recomputed: the sign `σ (p, q) = (-1) ^ (p * q)` is provided by the complex shape sign
   formalism, and the flip of a totalized bifunctor (`TotalComplexSymmetry`, `BifunctorFlip`,
   possibly still to be migrated from mathlib PR #25848) provides the isomorphism, which is
   combined with the braiding of `C` transported through `mapBifunctor`. The braided axioms
   then reduce on homogeneous summands to the hexagons in `C` together with
   `(-1) ^ (p * (q + r)) = (-1) ^ (p * q) * (-1) ^ (p * r)` and its mirror image, and the
   symmetry axiom to the one in `C`, since `(-1) ^ (p * q) * (-1) ^ (q * p) = 1`.
2. **Descent to the homotopy category.** The braiding is an honest isomorphism of complexes
   and naturality, the hexagons and the symmetry relation are equalities of chain maps, so
   they are preserved by the quotient functor; what has to be checked is the compatibility
   with the associator and unitors already constructed on `K(C)`.
3. **Transport through the derived tensor.** Write `T := curriedTensor K(C)` and
   `T^L := curriedTensor D(C)`, so that `T^L` is the binary left derived functor of `T`. Prove
   first that `T^L.flip` is a binary left derived functor of `T.flip` (the one piece of API
   glue this step needs), then lift the braiding `T ≅ T.flip` of `K(C)` in both directions by
   the binary left derived lifting property; the two lifts are mutually inverse by binary
   left derived uniqueness. The two hexagons are identities of natural transformations in
   three variables, hence follow by *ternary* left derived extensionality, as in the
   coherence proofs of the derived monoidal structure; the symmetry axiom is an identity in
   two variables, so binary extensionality suffices and no further derivability hypothesis is
   needed.

Step 3 is the reusable one and is best formulated abstractly: a braided (symmetric) source
together with a localization carrying a derived monoidal structure yields a braided
(symmetric) derived monoidal category. The instances below are then its application to
`DerivedCategory.Qh`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

/-- The derived category of a braided abelian monoidal category is braided for the derived
tensor product: the braiding of `C` induces the Koszul braiding on complexes, which descends
to `K(C)` and is transported to `D(C)` by the universal property of the binary left derived
functor. -/
noncomputable instance braidedCategory [BraidedCategory C] :
    BraidedCategory (DerivedCategory C) :=
  sorry

/-- The derived category of a symmetric abelian monoidal category is symmetric for the
derived tensor product. The braiding is the one of `DerivedCategory.braidedCategory`; only
the symmetry axiom has to be proved, and being an identity in two variables, it follows from
the symmetry of `K(C)` by binary left derived extensionality. -/
noncomputable instance symmetricCategory [SymmetricCategory C] :
    SymmetricCategory (DerivedCategory C) where
  symmetry X Y := sorry

end DerivedCategory
