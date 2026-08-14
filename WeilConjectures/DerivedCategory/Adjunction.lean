/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.DerivedCategory.RightDerivedFunctor.Defs

/-!
# Adjunctions of derived functors

Given an adjunction `adj : f ⊣ g` of additive functors between abelian categories, this
file lifts `adj` through the stages of the derived formalism:

* `Adjunction.mapHomologicalComplex`: the induced adjunction
  `f.mapHomologicalComplex c ⊣ g.mapHomologicalComplex c` between the categories of
  homological complexes, with unit and counit given degreewise.
* `Adjunction.mapHomotopyCategory`: the induced adjunction
  `f.mapHomotopyCategory c ⊣ g.mapHomotopyCategory c` between the homotopy categories,
  whenever the quotient functors to the homotopy categories are localizations with
  respect to homotopy equivalences (which holds, in particular, for the complex shapes
  `ComplexShape.up ℤ` and `ComplexShape.down ι`); it is obtained from the previous
  adjunction by descent along the localization functors, using
  `Adjunction.localization`.
* `Adjunction.derivedAdjunction`: the derived adjunction

  `f.leftDerivedFunctor ⊣ g.rightDerivedFunctor`

  between the total derived functors on the unbounded derived categories, where

  - the source category is monoidal and admits functorial flat resolutions, and `f`
    preserves K-flat quasi-isomorphisms (`f.PreservesKFlatQuasiIso`), so that the total
    left derived functor is defined
    (see `WeilConjectures.DerivedCategory.LeftDerivedFunctor.Defs`);
  - the target category has K-injective resolutions, so that the total right derived
    functor is defined (see `WeilConjectures.DerivedCategory.RightDerivedFunctor.Defs`).

  It is constructed by applying the abstract theorem `Adjunction.derived` to the
  adjunction `adj.mapHomotopyCategory (.up ℤ)`. The two "absoluteness" hypotheses of
  `Adjunction.derived` are verified using the good-object isomorphism criteria of the
  K-flat left derivability structure (for `f.leftDerivedFunctor ⋙ g.rightDerivedFunctor`)
  and of the K-injective right derivability structure
  (for `g.rightDerivedFunctor ⋙ f.leftDerivedFunctor`): in both cases, the comparison
  natural transformation is an isomorphism on K-flat (respectively K-injective) complexes
  because the counit `f.leftDerivedFunctorCounit` (respectively the unit
  `g.rightDerivedFunctorUnit`) is.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Category Limits MonoidalCategory Abelian

namespace CategoryTheory

section MapHomologicalComplex

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] {ι : Type*} (c : ComplexShape ι)

/-- An adjunction `G ⊣ F` of additive functors induces an adjunction
`G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c` between the induced functors on
categories of homological complexes. -/
noncomputable def Adjunction.mapHomologicalComplex {G : D ⥤ C} {F : C ⥤ D} (adj : G ⊣ F)
    [G.Additive] [F.Additive] :
    G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c where
  unit :=
    { app := fun M =>
        { f := fun n => adj.unit.app (M.X n)
          comm' := fun i j _ => (adj.unit.naturality (M.d i j)).symm }
      naturality := fun M N φ => by
        ext n
        exact adj.unit.naturality (φ.f n) }
  counit :=
    { app := fun K =>
        { f := fun n => adj.counit.app (K.X n)
          comm' := fun i j _ => (adj.counit.naturality (K.d i j)).symm }
      naturality := fun K L ψ => by
        ext n
        exact adj.counit.naturality (ψ.f n) }
  left_triangle_components X := by
    ext n
    exact adj.left_triangle_components (X.X n)
  right_triangle_components Y := by
    ext n
    exact adj.right_triangle_components (Y.X n)

end MapHomologicalComplex

section MapHomotopyCategory

variable {ι : Type*} {V W : Type*} [Category V] [Category W]
  [Preadditive V] [Preadditive W]
  {f : V ⥤ W} {g : W ⥤ V} [f.Additive] [g.Additive]

variable (f) in
/-- The 2-commutative square expressing that `Functor.mapHomotopyCategory`
descends `Functor.mapHomologicalComplex` along the quotient functors to the
homotopy categories. -/
instance Functor.catCommSqMapHomotopyCategory (c : ComplexShape ι) :
    CatCommSq (f.mapHomologicalComplex c) (HomotopyCategory.quotient V c)
      (HomotopyCategory.quotient W c) (f.mapHomotopyCategory c) :=
  ⟨(f.mapHomotopyCategoryFactors c).symm⟩

/-- An adjunction `f ⊣ g` between additive functors induces an adjunction
between the induced functors on homotopy categories, whenever the quotient
functors to the homotopy categories are localizations with respect to
homotopy equivalences. This holds, in particular, for cochain complexes
indexed by `ℤ` (`ComplexShape.up ℤ`). -/
noncomputable def Adjunction.mapHomotopyCategory (adj : f ⊣ g) (c : ComplexShape ι)
    [(HomotopyCategory.quotient V c).IsLocalization
      (HomologicalComplex.homotopyEquivalences V c)]
    [(HomotopyCategory.quotient W c).IsLocalization
      (HomologicalComplex.homotopyEquivalences W c)] :
    f.mapHomotopyCategory c ⊣ g.mapHomotopyCategory c :=
  (adj.mapHomologicalComplex c).localization
    (HomotopyCategory.quotient V c) (HomologicalComplex.homotopyEquivalences V c)
    (HomotopyCategory.quotient W c) (HomologicalComplex.homotopyEquivalences W c)
    (f.mapHomotopyCategory c) (g.mapHomotopyCategory c)

end MapHomotopyCategory

section DerivedAdjunction

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

end DerivedAdjunction

end CategoryTheory
