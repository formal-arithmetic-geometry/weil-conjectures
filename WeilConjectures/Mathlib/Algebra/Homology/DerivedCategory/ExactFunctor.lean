/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Functoriality of `mapDerivedCategory`

For exact functors between abelian categories, the induced functor
`Functor.mapDerivedCategory` on derived categories is functorial:

- `CategoryTheory.Functor.mapDerivedCategoryNatIso`: an isomorphism `F ≅ G` of exact
  functors induces an isomorphism `F.mapDerivedCategory ≅ G.mapDerivedCategory`.
- `CategoryTheory.Functor.mapDerivedCategoryCompIso`: the composition isomorphism
  `(F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory`.
- `CategoryTheory.Functor.mapDerivedCategoryPlus`: the restriction of
  `F.mapDerivedCategory` to the bounded below derived categories, with the compatibility
  isomorphism `CategoryTheory.Functor.mapDerivedCategoryPlusCompatibility`.
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

section Plus

variable (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact functor between abelian categories preserves bounded below objects of the
derived categories: an object isomorphic to a complex concentrated in degrees `≥ n` is
sent to an object with the same property. -/
lemma isGE_mapDerivedCategory_obj (X : DerivedCategory C) (n : ℤ) [X.IsGE n] :
    (F.mapDerivedCategory.obj X).IsGE n := by
  obtain ⟨K, hK, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE n
  have : DerivedCategory.TStructure.t.IsGE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj K) n :=
    inferInstanceAs (DerivedCategory.IsGE (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) n)
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (F.mapDerivedCategory.mapIso e ≪≫ F.mapDerivedCategoryFactors.app K).symm n

/-- The functor induced on the bounded below derived categories by an exact functor
between abelian categories: the restriction of `F.mapDerivedCategory` to
`DerivedCategory.Plus`, which is well defined since an exact functor preserves bounded
below objects. -/
noncomputable def mapDerivedCategoryPlus :
    DerivedCategory.Plus C ⥤ DerivedCategory.Plus D :=
  DerivedCategory.TStructure.t.plus.lift
    (DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory) (by
      rintro ⟨X, n, hn⟩
      exact ⟨n, F.isGE_mapDerivedCategory_obj X n⟩)

/-- The restriction `F.mapDerivedCategoryPlus` of `F.mapDerivedCategory` to the bounded
below derived categories is compatible with the inclusions. -/
noncomputable def mapDerivedCategoryPlusCompatibility :
    F.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ F.mapDerivedCategory :=
  Iso.refl _

end Plus

end CategoryTheory.Functor
