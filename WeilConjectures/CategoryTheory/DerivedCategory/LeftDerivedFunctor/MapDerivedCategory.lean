/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The total left derived functor of an exact functor is `mapDerivedCategory`

An exact functor `F : C ⥤ D` between abelian categories induces a functor
`F.mapDerivedCategory : DerivedCategory C ⥤ DerivedCategory D` directly, by applying `F`
levelwise (`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`). When the monoidal
abelian category `C` moreover admits functorial flat resolutions, `F` also has a total
left derived functor `F.leftDerivedFunctor` computed via K-flat resolutions
(`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`). This file shows that
the two constructions agree:

- `Functor.leftDerivedFunctorIsoMapDerivedCategory`: the canonical isomorphism
  `F.leftDerivedFunctor ≅ F.mapDerivedCategory`, obtained from uniqueness of left derived
  functors: since the comparison `F.mapDerivedCategoryFactorsh` is an isomorphism,
  `F.mapDerivedCategory` is *itself* a left derived functor of
  `F.mapHomotopyCategory ⋙ Qh`.
- `Functor.isIso_leftDerivedFunctorCounit`: consequently, the counit of the left derived
  functor of an exact functor is an isomorphism everywhere (not only on K-flat
  complexes).

From this compatibility we derive, still for exact functors, the isomorphisms expressing
that left derivation commutes with the constructions preserved by `mapDerivedCategory`
(themselves in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
`Functor.mapDerivedCategoryNatIso`, `Functor.mapDerivedCategoryCompIso` and
`Functor.mapDerivedCategoryHomologyFunctorIso`):

- `Functor.leftDerivedFunctorNatIso`, `Functor.leftDerivedFunctorCompIso`,
  `Functor.leftDerivedFunctorHomologyFunctorIso`,
  `Functor.singleFunctorCompLeftDerivedFunctorIso`: the corresponding statements for the
  total left derived functor, obtained by transport along the compatibility isomorphism.

These are the general inputs needed to identify the derived pullback `Lg^*` of étale
sheaves (which is left derived from the *exact* functor `g^*`) with the levelwise
functor, and to obtain its composition, homology, and single-degree compatibilities; see
`WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`.

-/

@[expose] public section

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open MonoidalCategory

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

section Compatibility

/-- For an *exact* functor `F` between abelian categories, the total left derived
functor computed via K-flat resolutions is canonically isomorphic to the functor
`F.mapDerivedCategory` induced by applying `F` levelwise. Indeed, since
`F.mapDerivedCategoryFactorsh` is an isomorphism, `F.mapDerivedCategory` is itself a
left derived functor of `F.mapHomotopyCategory ⋙ Qh`, and left derived functors are
unique up to canonical isomorphism. -/
noncomputable def leftDerivedFunctorIsoMapDerivedCategory :
    F.leftDerivedFunctor ≅ F.mapDerivedCategory :=
  leftDerivedUnique F.mapDerivedCategory F.leftDerivedFunctor F.leftDerivedFunctorCounit
    F.mapDerivedCategoryFactorsh.hom (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

@[reassoc (attr := simp)]
lemma leftDerivedFunctorIsoMapDerivedCategory_hom_fac :
    Functor.whiskerLeft DerivedCategory.Qh F.leftDerivedFunctorIsoMapDerivedCategory.hom ≫
      F.mapDerivedCategoryFactorsh.hom = F.leftDerivedFunctorCounit := by
  simp [leftDerivedFunctorIsoMapDerivedCategory]

/-- The counit of the total left derived functor of an *exact* functor is an isomorphism
everywhere: the left derived functor is computed by applying the functor levelwise, with
no resolution needed. -/
instance isIso_leftDerivedFunctorCounit : IsIso F.leftDerivedFunctorCounit := by
  rw [← F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  infer_instance

/-- An isomorphism `F ≅ G` of exact functors induces an isomorphism
`F.leftDerivedFunctor ≅ G.leftDerivedFunctor` of the total left derived functors. -/
noncomputable def leftDerivedFunctorNatIso {G : C ⥤ D} [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.leftDerivedFunctor ≅ G.leftDerivedFunctor :=
  F.leftDerivedFunctorIsoMapDerivedCategory ≪≫ mapDerivedCategoryNatIso e ≪≫
    G.leftDerivedFunctorIsoMapDerivedCategory.symm

/-- The total left derived functor of an exact functor commutes with the homology
functors: the canonical isomorphism
`H^n(-) ⋙ F ≅ F.leftDerivedFunctor ⋙ H^n(-)` of functors `DerivedCategory C ⥤ D`. -/
noncomputable def leftDerivedFunctorHomologyFunctorIso (n : ℤ) :
    DerivedCategory.homologyFunctor C n ⋙ F ≅
      F.leftDerivedFunctor ⋙ DerivedCategory.homologyFunctor D n :=
  F.mapDerivedCategoryHomologyFunctorIso n ≪≫
    isoWhiskerRight F.leftDerivedFunctorIsoMapDerivedCategory.symm
      (DerivedCategory.homologyFunctor D n)

/-- The total left derived functor of an exact functor commutes with the single-degree
embeddings: the canonical isomorphism
`(-)[0] ⋙ F.leftDerivedFunctor ≅ F ⋙ (-)[0]` of functors `C ⥤ DerivedCategory D`. -/
noncomputable def singleFunctorCompLeftDerivedFunctorIso :
    DerivedCategory.singleFunctor C 0 ⋙ F.leftDerivedFunctor ≅
      F ⋙ DerivedCategory.singleFunctor D 0 :=
  isoWhiskerLeft (DerivedCategory.singleFunctor C 0)
      F.leftDerivedFunctorIsoMapDerivedCategory ≪≫
    F.mapDerivedCategorySingleFunctor 0

/-- The total left derived functor of an additive equivalence of abelian categories is an
equivalence of derived categories: it is isomorphic to `F.mapDerivedCategory`. -/
instance isEquivalence_leftDerivedFunctor [F.IsEquivalence] : F.leftDerivedFunctor.IsEquivalence :=
  isEquivalence_of_iso F.leftDerivedFunctorIsoMapDerivedCategory.symm

end Compatibility

section Composition

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

/-- The composition isomorphism
`(F ⋙ G).leftDerivedFunctor ≅ F.leftDerivedFunctor ⋙ G.leftDerivedFunctor` for exact
functors between abelian categories with functorial flat resolutions, obtained from
`mapDerivedCategoryCompIso` by transport along the compatibility isomorphisms. -/
noncomputable def leftDerivedFunctorCompIso (G : D ⥤ E) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).leftDerivedFunctor ≅ F.leftDerivedFunctor ⋙ G.leftDerivedFunctor :=
  (F ⋙ G).leftDerivedFunctorIsoMapDerivedCategory ≪≫ mapDerivedCategoryCompIso F G ≪≫
    isoWhiskerRight F.leftDerivedFunctorIsoMapDerivedCategory.symm G.mapDerivedCategory ≪≫
    isoWhiskerLeft F.leftDerivedFunctor G.leftDerivedFunctorIsoMapDerivedCategory.symm

end Composition

end CategoryTheory.Functor
