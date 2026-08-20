/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-!
# Adjunctions of derived functors

Given an adjunction `adj : f ⊣ g` of additive functors between abelian categories, this
file lifts `adj` through the stages of the derived formalism:

* `Adjunction.mapHomotopyCategory`: the induced adjunction
  `f.mapHomotopyCategory c ⊣ g.mapHomotopyCategory c` between the homotopy categories,
  whenever the quotient functors to the homotopy categories are localizations with
  respect to homotopy equivalences (which holds, in particular, for the complex shapes
  `ComplexShape.up ℤ` and `ComplexShape.down ι`); it is obtained from the adjunction
  `Adjunction.mapHomologicalComplex` between the categories of homological complexes
  (`WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`) by descent along the
  localization functors, using `Adjunction.localization`.
* `Adjunction.derivedAdjunction`: the derived adjunction

  `f.leftDerivedFunctor ⊣ g.rightDerivedFunctor`

  between the total derived functors on the unbounded derived categories, where

  - the source category is monoidal and admits functorial flat resolutions, and `f`
    preserves K-flat quasi-isomorphisms (`f.PreservesKFlatQuasiIso`), so that the total
    left derived functor is defined
    (see `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`);
  - the target category has K-injective resolutions, so that the total right derived
    functor is defined
    (see `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`).

  It is constructed by applying the abstract theorem `Adjunction.derived` to the
  adjunction `adj.mapHomotopyCategory (.up ℤ)`. The two "absoluteness" hypotheses of
  `Adjunction.derived` are verified using the good-object isomorphism criteria of the
  K-flat left derivability structure (for `f.leftDerivedFunctor ⋙ g.rightDerivedFunctor`)
  and of the K-injective right derivability structure
  (for `g.rightDerivedFunctor ⋙ f.leftDerivedFunctor`): in both cases, the comparison
  natural transformation is an isomorphism on K-flat (respectively K-injective) complexes
  because the counit `f.leftDerivedFunctorCounit` (respectively the unit
  `g.rightDerivedFunctorUnit`) is.
* `Adjunction.derivedAdjunctionPlus`: for `f` moreover *exact*, the bounded below
  derived adjunction `f.mapDerivedCategoryPlus ⊣ g.rightDerivedFunctorPlus`, obtained by
  restricting the derived adjunction along the inclusions of the bounded below derived
  categories, using the identification of the left derived functor of the exact functor
  `f` with `f.mapDerivedCategory` and the compatibility of `g.rightDerivedFunctorPlus`
  with the unbounded right derived functor.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Category Limits MonoidalCategory Abelian

namespace CategoryTheory

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

/-- The bounded below derived adjunction of an adjoint pair `adj : f ⊣ g` of additive
functors between abelian categories, where `f` is moreover *exact*:

`f.mapDerivedCategoryPlus ⊣ g.rightDerivedFunctorPlus`

between the functor induced by `f` on the bounded below derived categories and the right
derived functor of `g` on the bounded below derived categories. It is obtained by
restricting the unbounded derived adjunction `Adjunction.derivedAdjunction` along the
inclusions of the bounded below derived categories: since `f` is exact, its total left
derived functor identifies with `f.mapDerivedCategory`
(`Functor.leftDerivedFunctorIsoMapDerivedCategory`), which restricts to the bounded
below derived categories as `f.mapDerivedCategoryPlus`; on the right adjoint side, the
restriction of `g.rightDerivedFunctor` identifies with `g.rightDerivedFunctorPlus` by
`Functor.rightDerivedFunctorPlusCompatibility`. -/
noncomputable def Adjunction.derivedAdjunctionPlus {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g)
    [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [EnoughInjectives D] :
    f.mapDerivedCategoryPlus ⊣ g.rightDerivedFunctorPlus :=
  Adjunction.restrictFullyFaithful
    (adj.derivedAdjunction.ofNatIsoLeft f.leftDerivedFunctorIsoMapDerivedCategory)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    f.mapDerivedCategoryPlusCompatibility.symm
    g.rightDerivedFunctorPlusCompatibility.symm

end DerivedAdjunction

end CategoryTheory
