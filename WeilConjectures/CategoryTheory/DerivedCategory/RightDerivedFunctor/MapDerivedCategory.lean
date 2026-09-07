/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The total right derived functor of an exact functor is `mapDerivedCategory`

An exact functor `F : C ⥤ D` between abelian categories induces a functor
`F.mapDerivedCategory : DerivedCategory C ⥤ DerivedCategory D` directly, by applying `F`
levelwise (`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`). When the abelian
category `C` moreover has K-injective resolutions, `F` also has a total right derived
functor `F.rightDerivedFunctor` computed via K-injective resolutions
(`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`). This file
shows that the two constructions agree:

- `Functor.rightDerivedFunctorIsoMapDerivedCategory`: the canonical isomorphism
  `F.rightDerivedFunctor ≅ F.mapDerivedCategory`, obtained from uniqueness of right
  derived functors: since the comparison `F.mapDerivedCategoryFactorsh` is an
  isomorphism, `F.mapDerivedCategory` is *itself* a right derived functor of
  `F.mapHomotopyCategory ⋙ Qh`.
- `Functor.isIso_rightDerivedFunctorUnit`: consequently, the unit of the right derived
  functor of an exact functor is an isomorphism everywhere (not only on K-injective
  complexes).

From this compatibility we derive, still for exact functors, the isomorphisms expressing
that right derivation commutes with the constructions preserved by `mapDerivedCategory`
(themselves in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
`Functor.mapDerivedCategoryNatIso`, `Functor.mapDerivedCategoryCompIso` and
`Functor.mapDerivedCategoryHomologyFunctorIso`):

- `Functor.rightDerivedFunctorHomologyFunctorIso` and
  `Functor.singleFunctorCompRightDerivedFunctorIso`: the commutation of the total right
  derived functor with the homology functors and with the single-degree embeddings.
- `Functor.rightDerivedFunctorCompIsoOfExact`: the composition isomorphism
  `R(F ⋙ G) ≅ RF ⋙ RG` for *exact* `F` and `G`. This is the exact-functor counterpart of
  `Functor.rightDerivedFunctorCompIso` of
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`, which holds
  for arbitrary additive functors but takes `F.PreservesKInjectiveComplexes` instead of
  exactness.

The functoriality of `rightDerivedFunctor` in natural isomorphisms is *not* repeated
here: `Functor.rightDerivedFunctorNatIso` of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` already
provides it for arbitrary additive functors.

This is the right-derived counterpart of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory`.
Note the asymmetry in the hypotheses: left derivation via K-flat resolutions requires the
source category to carry a monoidal structure with functorial flat resolutions, while
right derivation via K-injective resolutions only requires
`CategoryTheory.Abelian.HasKInjectiveResolutions`.

-/

@[expose] public section

universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Abelian Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

section Compatibility

variable [HasKInjectiveResolutions C]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The functor `F.mapDerivedCategory` induced by an exact functor `F` is a right derived
functor of `F.mapHomotopyCategory ⋙ Qh`, with unit the inverse of the comparison
`F.mapDerivedCategoryFactorsh`: the unit is an isomorphism, and `Qh` is a localization
functor for quasi-isomorphisms. -/
instance isRightDerivedFunctor_mapDerivedCategory :
    F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactorsh

/-- For an *exact* functor `F` between abelian categories, the total right derived
functor computed via K-injective resolutions is canonically isomorphic to the functor
`F.mapDerivedCategory` induced by applying `F` levelwise. Indeed, since
`F.mapDerivedCategoryFactorsh` is an isomorphism, `F.mapDerivedCategory` is itself a
right derived functor of `F.mapHomotopyCategory ⋙ Qh`, and right derived functors are
unique up to canonical isomorphism. -/
noncomputable def rightDerivedFunctorIsoMapDerivedCategory :
    F.rightDerivedFunctor ≅ F.mapDerivedCategory :=
  rightDerivedUnique F.rightDerivedFunctor F.mapDerivedCategory F.rightDerivedFunctorUnit
    F.mapDerivedCategoryFactorsh.inv (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

@[reassoc (attr := simp)]
lemma rightDerivedFunctorIsoMapDerivedCategory_hom_fac :
    F.rightDerivedFunctorUnit ≫
        Functor.whiskerLeft DerivedCategory.Qh
          F.rightDerivedFunctorIsoMapDerivedCategory.hom =
      F.mapDerivedCategoryFactorsh.inv := by
  simp [rightDerivedFunctorIsoMapDerivedCategory]

/-- The unit of the total right derived functor of an *exact* functor is an isomorphism
everywhere: the right derived functor is computed by applying the functor levelwise, with
no resolution needed. -/
instance isIso_rightDerivedFunctorUnit : IsIso F.rightDerivedFunctorUnit := by
  have : IsIso (F.rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh
        F.rightDerivedFunctorIsoMapDerivedCategory.hom) := by
    rw [F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (Functor.whiskerLeft DerivedCategory.Qh
      F.rightDerivedFunctorIsoMapDerivedCategory.hom)

/-- The total right derived functor of an exact functor commutes with the homology
functors: the canonical isomorphism
`H^n(-) ⋙ F ≅ F.rightDerivedFunctor ⋙ H^n(-)` of functors `DerivedCategory C ⥤ D`. -/
noncomputable def rightDerivedFunctorHomologyFunctorIso (n : ℤ) :
    DerivedCategory.homologyFunctor C n ⋙ F ≅
      F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor D n :=
  F.mapDerivedCategoryHomologyFunctorIso n ≪≫
    isoWhiskerRight F.rightDerivedFunctorIsoMapDerivedCategory.symm
      (DerivedCategory.homologyFunctor D n)

/-- The total right derived functor of an exact functor commutes with the single-degree
embeddings: the canonical isomorphism
`(-)[0] ⋙ F.rightDerivedFunctor ≅ F ⋙ (-)[0]` of functors `C ⥤ DerivedCategory D`. -/
noncomputable def singleFunctorCompRightDerivedFunctorIso :
    DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor ≅
      F ⋙ DerivedCategory.singleFunctor D 0 :=
  isoWhiskerLeft (DerivedCategory.singleFunctor C 0)
      F.rightDerivedFunctorIsoMapDerivedCategory ≪≫
    F.mapDerivedCategorySingleFunctor 0

end Compatibility

section Composition

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]

/-- The composition isomorphism
`(F ⋙ G).rightDerivedFunctor ≅ F.rightDerivedFunctor ⋙ G.rightDerivedFunctor` for exact
functors between abelian categories with K-injective resolutions, obtained from
`mapDerivedCategoryCompIso` by transport along the compatibility isomorphisms.

This does not assume `F.PreservesKInjectiveComplexes`, unlike
`Functor.rightDerivedFunctorCompIso` of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`, which in turn
assumes `F.PreservesKInjectiveComplexes` instead of exactness. -/
noncomputable def rightDerivedFunctorCompIsoOfExact (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (F ⋙ G).rightDerivedFunctor ≅ F.rightDerivedFunctor ⋙ G.rightDerivedFunctor :=
  (F ⋙ G).rightDerivedFunctorIsoMapDerivedCategory ≪≫ mapDerivedCategoryCompIso F G ≪≫
    isoWhiskerRight F.rightDerivedFunctorIsoMapDerivedCategory.symm G.mapDerivedCategory ≪≫
    isoWhiskerLeft F.rightDerivedFunctor G.rightDerivedFunctorIsoMapDerivedCategory.symm

end Composition

end CategoryTheory.Functor
