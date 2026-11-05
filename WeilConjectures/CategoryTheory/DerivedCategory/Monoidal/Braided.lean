/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.CategoryTheory.Monoidal.Braided.Multifunctor
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric

/-!
# The braiding of the derived tensor product, and the symmetry of `D(C)`

Let `C` be an abelian monoidal category satisfying the hypotheses under which the derived
category `D(C)` is monoidal for the derived tensor product, i.e. those of
`WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`: the derived tensor
product is the binary left derived functor of the tensor product on
`K(C) := HomotopyCategory C (ComplexShape.up ℤ)`. This file constructs, for `C` braided, the
braiding isomorphisms of `K(C)` and of `D(C)` as natural isomorphisms of bifunctors, and states
that `D(C)` is symmetric if `C` is.

The construction follows the chain
`C braided ⟹ Koszul braiding on CochainComplex C ℤ ⟹ K(C) braided ⟹ D(C) braided`:

1. **The Koszul braiding on complexes (the step carrying the sign content).** The braiding of
   `C` cannot be transported degreewise: on the summand `X p ⊗ Y q` of the tensor product of
   complexes the correct map is `(-1) ^ (p * q) • β_ (X p) (Y q)`, the Koszul sign being what
   makes the flip commute with the total differential. It is *assembled*, not recomputed
   (`HomologicalComplex.braiding`): the braiding of `C` transported through `mapBifunctor`
   (`HomologicalComplex.mapBifunctorIsoOfIso`), followed by the flip isomorphism
   `HomologicalComplex.mapBifunctorFlipIso` of the total complex, which carries the sign
   `σ` of the complex shape sign formalism.
2. **Descent to the homotopy category.** The braiding is an honest isomorphism of complexes,
   natural in both variables, so it descends along the quotient functor
   (`HomotopyCategory.MonoidalCategory.braiding`, via `Quotient.natIsoLift₂`).
3. **Transport through the derived tensor.** Write `T := curriedTensor K(C)` and
   `T^L := curriedTensor D(C)`, so that `T^L` is the binary left derived functor of `T`. A
   morphism `τ : T.flip ⟶ T` lifts to `T^L.flip ⟶ T^L` by the binary left derived lifting
   property (`DerivedMonoidal.flipLift`). The derived braiding `DerivedMonoidal.braiding` is
   the lift of the braiding of `K(C)`, evaluated at swapped arguments, with inverse the lift of
   its inverse; the two are mutually inverse by binary left derived uniqueness
   (`Functor.leftDerived₂_ext`).

## Implementation notes

No braided structure is declared here. For a general complex shape `c`, the sign of
`TotalComplexShapeSymmetry c c c` is only determined up to a global sign, and replacing `σ` by
`-σ` breaks the hexagon identities, so the braiding of `K(C)` is only claimed to be braided for
`c = ComplexShape.up ℤ`, where this is proved (`HomotopyCategory.braidedCategory`). The braided
structure on `D(C)` is the proved `DerivedCategory.braidedCategory'` (see
`CategoryTheory.DerivedMonoidal.braidedCategory'`); it is not a global instance, and the
symmetric structure `DerivedCategory.symmetricCategory` built on it is a `def` as well.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

/-! ### Natural transformations between bifunctors on quotient categories -/

namespace CategoryTheory.Quotient

open _root_.CategoryTheory.Functor

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  (r₁ : HomRel C₁) (r₂ : HomRel C₂)

end CategoryTheory.Quotient

/-! ### The Koszul braiding on complexes -/

namespace HomologicalComplex

section MapBifunctor

variable {C₁ C₂ D : Type*} [Category C₁] [Category C₂] [Category D]
  {I₁ I₂ J : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  {F G : C₁ ⥤ C₂ ⥤ D} [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  [G.PreservesZeroMorphisms] [∀ X₁, (G.obj X₁).PreservesZeroMorphisms]
  (e : F ≅ G) (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)

variable (c : ComplexShape J) [TotalComplexShape c₁ c₂ c] [DecidableEq J]
  [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor K₁ K₂ G c]

variable {K₁ K₂} {L₁ : HomologicalComplex C₁ c₁} {L₂ : HomologicalComplex C₂ c₂}
  (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) [HasMapBifunctor L₁ L₂ F c] [HasMapBifunctor L₁ L₂ G c]

end MapBifunctor

section Braiding

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]
  [MonoidalPreadditive C] {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I}
  [c.TensorSigns] [TotalComplexShapeSymmetry c c c]

end Braiding

end HomologicalComplex

/-! ### The braiding on the homotopy category -/

namespace HomotopyCategory.MonoidalCategory

variable (C : Type*) [Category C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [(curriedTensor C).Additive]
  [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] (c : ComplexShape I) [c.TensorSigns]
  [∀ (X₁ X₂ : GradedObject I C), X₁.HasTensor X₂]
  [∀ (X₁ : C), PreservesColimit (Functor.empty C) ((curriedTensor C).obj X₁)]
  [∀ (X₂ : C), PreservesColimit (Functor.empty C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃] [DecidableEq I]
  [∀ (K₁ K₂ : HomologicalComplex C c),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor C) c]
  [BraidedCategory C] [MonoidalPreadditive C] [TotalComplexShapeSymmetry c c c]

end HomotopyCategory.MonoidalCategory

/-! ### Transport of a braiding through a derived monoidal structure -/

namespace CategoryTheory.DerivedMonoidal

open _root_.CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W] [W.ContainsIdentities]
  [L.HasDerivedMonoidalCategory W]

variable [BraidedCategory C]

end CategoryTheory.DerivedMonoidal

/-! ### The derived category -/

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

local instance hasColimitsOfSize_symmetricCategory : HasColimitsOfSize.{0, 0} C :=
  hasColimitsOfSizeShrink C

variable [HasDerivedCategory.{w} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [SymmetricCategory C] [Abelian.HasFunctorialFlatResolution C]

end DerivedCategory
