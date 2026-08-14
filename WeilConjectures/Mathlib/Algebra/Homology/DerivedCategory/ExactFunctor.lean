/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Functoriality of `mapDerivedCategory`

For exact functors between abelian categories, the induced functor
`Functor.mapDerivedCategory` on derived categories is functorial:

- `CategoryTheory.Functor.mapDerivedCategoryNatIso`: an isomorphism `F ≅ G` of exact
  functors induces an isomorphism `F.mapDerivedCategory ≅ G.mapDerivedCategory`.
- `CategoryTheory.Functor.mapDerivedCategoryCompIso`: the composition isomorphism
  `(F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory`.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

/-- An isomorphism `F ≅ G` of exact functors between abelian categories induces an
isomorphism `F.mapDerivedCategory ≅ G.mapDerivedCategory` of the functors induced on
derived categories, compatibly with the localization functors. -/
noncomputable def mapDerivedCategoryNatIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- The composition isomorphism
`(F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory` for exact
functors between abelian categories: both sides are induced by
`(F ⋙ G).mapHomologicalComplex` on the localizations. -/
noncomputable def mapDerivedCategoryCompIso (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (F.mapDerivedCategory ⋙ G.mapDerivedCategory) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight F.mapDerivedCategoryFactors G.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (ComplexShape.up ℤ)) DerivedCategory.Q⟩
  Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (F ⋙ G).mapDerivedCategory (F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (Iso.refl _)

end CategoryTheory.Functor
