/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.DerivedCategory.HomotopyAdjunction
public import WeilConjectures.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.DerivedCategory.RightDerivedFunctor.Defs

/-!
# The adjunction between total derived functors of an adjoint pair

Let `f : C ⥤ D` and `g : D ⥤ C` be an adjoint pair `adj : f ⊣ g` of additive
functors between abelian categories, where

* `C` is monoidal and admits functorial flat resolutions, and `f` preserves
  K-flat quasi-isomorphisms (`f.PreservesKFlatQuasiIso`), so that the total
  left derived functor `f.leftDerivedFunctor : DerivedCategory C ⥤
  DerivedCategory D` is defined (see
  `WeilConjectures.DerivedCategory.LeftDerivedFunctor.Defs`);
* `D` has K-injective resolutions, so that the total right derived functor
  `g.rightDerivedFunctor : DerivedCategory D ⥤ DerivedCategory C` is defined
  (see `WeilConjectures.DerivedCategory.RightDerivedFunctor.Defs`).

We construct the derived adjunction

`Adjunction.derivedAdjunction adj : f.leftDerivedFunctor ⊣ g.rightDerivedFunctor`

by applying the abstract theorem `Adjunction.derived` to the adjunction
`adj.mapHomotopyCategory (.up ℤ)` between the induced functors on homotopy
categories. The two "absoluteness" hypotheses of `Adjunction.derived` are
verified using the good-object isomorphism criteria of the K-flat left
derivability structure (for `f.leftDerivedFunctor ⋙ g.rightDerivedFunctor`)
and of the K-injective right derivability structure
(for `g.rightDerivedFunctor ⋙ f.leftDerivedFunctor`): in both cases, the
comparison natural transformation is an isomorphism on K-flat (respectively
K-injective) complexes because the counit `f.leftDerivedFunctorCounit`
(respectively the unit `g.rightDerivedFunctorUnit`) is.

-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Abelian

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (j : ℤ), HasColimitsOfShape
    (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j})) C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]
  (f : C ⥤ D) (g : D ⥤ C) [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]

namespace Functor

/-- The composition `f.leftDerivedFunctor ⋙ g.rightDerivedFunctor` is the
left derived functor of `(f.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
⋙ g.rightDerivedFunctor`: the required comparison natural transformation is
an isomorphism on K-flat complexes since `f.leftDerivedFunctorCounit` is.
This is the first "absoluteness" hypothesis of `Adjunction.derived`. -/
instance isLeftDerivedFunctor_leftDerivedFunctor_comp_rightDerivedFunctor :
    (f.leftDerivedFunctor ⋙ g.rightDerivedFunctor).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        whiskerRight f.leftDerivedFunctorCounit g.rightDerivedFunctor)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quasiIso C
    (ComplexShape.up ℤ)).localizerMorphismKFlat.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
      _ (fun P ↦ by
        have := f.derives_kFlat.isIso_of_isLeftDerivedFunctor f.leftDerivedFunctorCounit P
        exact inferInstanceAs
          (IsIso (𝟙 _ ≫ g.rightDerivedFunctor.map (f.leftDerivedFunctorCounit.app _))))

/-- The composition `g.rightDerivedFunctor ⋙ f.leftDerivedFunctor` is the
right derived functor of `(g.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
⋙ f.leftDerivedFunctor`: the required comparison natural transformation is
an isomorphism on K-injective complexes since `g.rightDerivedFunctorUnit` is.
This is the second "absoluteness" hypothesis of `Adjunction.derived`. -/
instance isRightDerivedFunctor_rightDerivedFunctor_comp_leftDerivedFunctor :
    (g.rightDerivedFunctor ⋙ f.leftDerivedFunctor).IsRightDerivedFunctor
      (whiskerRight g.rightDerivedFunctorUnit f.leftDerivedFunctor ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso D (ComplexShape.up ℤ)) :=
  (HomotopyCategory.KInjectives.localizerMorphism
    D).isRightDerivedFunctor_of_isRightDerivabilityStructure
      _ (fun I ↦ by
        have := (HomotopyCategory.KInjectives.localizerMorphism_derives
          (g.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh)).isIso_of_isRightDerivedFunctor g.rightDerivedFunctorUnit I
        exact inferInstanceAs
          (IsIso (f.leftDerivedFunctor.map (g.rightDerivedFunctorUnit.app _) ≫ 𝟙 _)))

end Functor

/-- The derived adjunction: an adjunction `f ⊣ g` of additive functors between
abelian categories, where `f` is left derivable via K-flat resolutions and `g`
is right derivable via K-injective resolutions, induces an adjunction

`f.leftDerivedFunctor ⊣ g.rightDerivedFunctor`

between the total derived functors on the unbounded derived categories. -/
noncomputable def Adjunction.derivedAdjunction {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g)
    [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso] :
    f.leftDerivedFunctor ⊣ g.rightDerivedFunctor :=
  (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derived
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso D (ComplexShape.up ℤ))
    f.leftDerivedFunctorCounit g.rightDerivedFunctorUnit

end CategoryTheory
