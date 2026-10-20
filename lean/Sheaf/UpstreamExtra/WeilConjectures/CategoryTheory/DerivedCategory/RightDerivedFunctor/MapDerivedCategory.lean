module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! Declarations of ours that lived in the upstream file `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

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
- `Functor.rightDerivedFunctorCompMapDerivedCategoryIso`: the composition isomorphism
  `R(F ⋙ G) ≅ RF ⋙ D(G)` for an arbitrary additive `F` and an *exact* `G`: right deriving a
  composite whose second factor is exact amounts to right deriving the first factor and
  applying the second levelwise.

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

end Compatibility

section Composition

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]

end Composition

section CompositionExactRight

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  [HasKInjectiveResolutions C]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

end CompositionExactRight

section RetainedComparison

variable {E : Type uE} [Category.{vE} E] [Abelian E]
 [HasDerivedCategory.{wE} E]
 [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]

/-- The retained exact-composition comparison agrees with the upstream direct one. -/
lemma rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived_eq
 (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
 [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
 rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived F G =
 rightDerivedFunctorCompMapDerivedCategoryIso F G := by
 apply Iso.ext
 apply (F ⋙ G).rightDerivedFunctor.rightDerived_ext
   (F ⋙ G).rightDerivedFunctorUnit (HomotopyCategory.quasiIso C (.up ℤ))
 ext J
 simp [rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived,
   rightDerivedFunctorCompMapDerivedCategoryIso, rightDerivedFunctorCompUnit,
   rightDerivedFunctorCompMapDerivedCategoryUnit, Category.assoc]
 have h := NatTrans.congr_app G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
   ((F.mapHomotopyCategory (.up ℤ)).obj J)
 dsimp only [NatTrans.comp_app, whiskerLeft_app] at h
 rw [← Category.assoc (G.rightDerivedFunctorUnit.app _) _ _, h]

end RetainedComparison

end CategoryTheory.Functor
