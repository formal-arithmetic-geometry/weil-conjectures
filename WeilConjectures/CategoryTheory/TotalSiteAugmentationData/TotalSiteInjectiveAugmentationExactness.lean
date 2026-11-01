/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exact injective augmentation on a total simplicial site

Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D79, lemma-augmentation-cech-complex
(blueprint: lem-trf-total-site-injective-augmentation-exactness).

The component categories and their coherent inverse-image geometric morphisms are
represented by `TotalSiteSystemData`; `a` gives the component augmentations and their
identity/composition coherences, and `totalInverse` identifies every component inverse
image with the induced total inverse image.  The displayed maps are the adjoint mates of
the component transition maps, and the augmentation is the mate of the degree-zero
counit component.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v w x y u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

namespace CategoryTheory

namespace TotalSiteAugmentationData

variable {A : SimplexCategoryᵒᵖ → Type v}
  [∀ i, Category.{w} (A i)] [∀ i, Abelian (A i)]
  {T : Type u} [Category.{w} T] [Abelian T]
  {D : Type x} [Category.{y} D] [Abelian D]
  (S : TotalSiteAugmentationData A T D)

/-- The coface map induced by the transition along the `i`-th face, using the
adjunction `(u face).inverse ⊣ (u face).direct` and the coherence `aComp`.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D79,
lemma-augmentation-cech-complex, Hom-adjunction construction
(blueprint: lem-trf-total-site-injective-augmentation-exactness). -/
noncomputable def faceMap (I : T) (p : ℕ) (i : Fin (p + 2)) :
    (S.a (Opposite.op (SimplexCategory.mk p))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk p))).obj I) ⟶
      (S.a (Opposite.op (SimplexCategory.mk (p + 1)))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk (p + 1)))).obj I) := by
  exact
    (S.a (Opposite.op (SimplexCategory.mk p))).direct.map
        ((S.u (SimplexCategory.δ i).op).adj.homEquiv _ _
          (S.system.transition I _ _ (SimplexCategory.δ i).op)) ≫
      (S.aComp (SimplexCategory.δ i).op).inv.app _

/-- The alternating face differential in degree `p`.
Source: Stacks Project, `spaces-simplicial.tex`, Tags 0D78 and 0D79,
lemma-simplicial-resolution-augmentation and lemma-augmentation-cech-complex
(blueprint: lem-trf-total-site-injective-augmentation-exactness). -/
noncomputable def differential (I : T) (p : ℕ) :
    (S.a (Opposite.op (SimplexCategory.mk p))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk p))).obj I) ⟶
      (S.a (Opposite.op (SimplexCategory.mk (p + 1)))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk (p + 1)))).obj I) :=
  ∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val • S.faceMap I p i

/-- The augmentation map, mate to the degree-zero component of the counit of the
induced total geometric morphism.
Source: Stacks Project, `spaces-simplicial.tex`, Tag 0D79,
lemma-augmentation-cech-complex, augmentation under the Hom adjunction
(blueprint: lem-trf-total-site-injective-augmentation-exactness). -/
noncomputable def augmentation (I : T) :
    S.total.direct.obj I ⟶
      (S.a (Opposite.op (SimplexCategory.mk 0))).direct.obj
        ((S.system.component (Opposite.op (SimplexCategory.mk 0))).obj I) :=
  (S.a (Opposite.op (SimplexCategory.mk 0))).adj.homEquiv (S.total.direct.obj I)
    ((S.system.component (Opposite.op (SimplexCategory.mk 0))).obj I)
    ((S.totalInverse (Opposite.op (SimplexCategory.mk 0))).hom.app
        (S.total.direct.obj I) ≫
      (S.system.component (Opposite.op (SimplexCategory.mk 0))).map
        (S.total.adj.counit.app I))

end TotalSiteAugmentationData

end CategoryTheory
