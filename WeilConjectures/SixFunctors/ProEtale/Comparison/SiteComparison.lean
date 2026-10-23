/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-!
# The bounded below site comparison

The comparison pullback `ν^* : Sh(X_ét, A) ⥤ Sh(X_proét, A)` is exact, its unit is invertible
and it sends injectives to `ν_*`-acyclic sheaves. Hence the unit of the bounded below derived
adjunction `D⁺(ν^*) ⊣ R⁺ν_*` is invertible, so that `D⁺(ν^*)` is fully faithful, and the derived
global sections of `X_ét` are those of `X_proét` composed with `D⁺(ν^*)`.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_comparisonAdjunction_derivedPlus_unit_app`: the derived unit
  `K ⟶ R⁺ν_* ν^* K` is an isomorphism for every `K` in `D⁺(X_ét)`.
- `AlgebraicGeometry.ProEtale.fullyFaithfulComparisonUpperStarMapDerivedCategoryPlus`:
  `D⁺(ν^*)` is fully faithful.
- `AlgebraicGeometry.ProEtale.rightDerivedFunctorPlusEtaleSectionsFunctorIso`:
  `RΓ(X_ét, -) ≅ RΓ(X_proét, ν^* -)` on `D⁺(X_ét)`.
- `AlgebraicGeometry.ProEtale.rightDerivedEtaleSectionsFunctorObjIso`: the induced isomorphism
  `H^q(X_ét, M) ≅ H^q(X_proét, ν^* M)` for an étale sheaf `M`.
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable (X : Scheme.{u})

/-- Blueprint `thm-weil-pbc-site-comparison`: Bounded-below site comparison

For every bounded below complex `K` of étale sheaves, the unit `K ⟶ R⁺ν_* ν^* K` of the derived
adjunction `D⁺(ν^*) ⊣ R⁺ν_*` is an isomorphism: the unit of `ν^* ⊣ ν_*` is invertible and `ν^*`
sends injective étale sheaves to `ν_*`-acyclic pro-étale sheaves. -/
theorem isIso_comparisonAdjunction_derivedPlus_unit_app
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    IsIso ((comparisonAdjunction A X).derivedPlus.unit.app K) := by
  have := isIso_comparisonAdjunction_unit A X
  exact (comparisonAdjunction A X).isIso_derivedPlus_unit_app_of_rightAcyclic
    (fun _ _ ↦ inferInstance) (fun I _ ↦ rightAcyclic_comparisonUpperStar_obj_of_injective A X I) K

/-- Blueprint `thm-weil-pbc-site-comparison`: the unit `id ⟶ R⁺ν_* ∘ D⁺(ν^*)` of the bounded
below derived comparison adjunction is a natural isomorphism. -/
instance isIso_comparisonAdjunction_derivedPlus_unit :
    IsIso (comparisonAdjunction A X).derivedPlus.unit :=
  (NatTrans.isIso_iff_isIso_app _).2 (isIso_comparisonAdjunction_derivedPlus_unit_app A X)

/-- Blueprint `thm-weil-pbc-site-comparison`: Bounded-below site comparison

The functor `D⁺(ν^*) : D⁺(X_ét) ⥤ D⁺(X_proét)` is fully faithful, the unit of the derived
adjunction `D⁺(ν^*) ⊣ R⁺ν_*` being invertible. -/
noncomputable def fullyFaithfulComparisonUpperStarMapDerivedCategoryPlus :
    D+(ν^*(X)[A]).FullyFaithful :=
  (comparisonAdjunction A X).derivedPlus.fullyFaithfulLOfIsIsoUnit

instance full_comparisonUpperStar_mapDerivedCategoryPlus : D+(ν^*(X)[A]).Full :=
  (fullyFaithfulComparisonUpperStarMapDerivedCategoryPlus A X).full

instance faithful_comparisonUpperStar_mapDerivedCategoryPlus : D+(ν^*(X)[A]).Faithful :=
  (fullyFaithfulComparisonUpperStarMapDerivedCategoryPlus A X).faithful

/-- Blueprint `lem-weil-pbc-comparison-global-cohomology`: Comparison of global cohomology

The derived global sections of the small étale site of `X` are the derived global sections of
the pro-étale site composed with `D⁺(ν^*)`: `RΓ(X_ét, K) ≅ RΓ(X_proét, ν^* K)` naturally in `K`
in `D⁺(X_ét)`. Since `Γ(X_proét, -) = Γ(X_ét, -) ∘ ν_*` and `ν_*` preserves injectives, we have
`RΓ(X_proét, -) ≅ RΓ(X_ét, -) ∘ R⁺ν_*`, and the derived unit `K ⟶ R⁺ν_* ν^* K` is invertible
(`isIso_comparisonAdjunction_derivedPlus_unit_app`). -/
noncomputable def rightDerivedFunctorPlusEtaleSectionsFunctorIso :
    R+(Etale.sectionsFunctor A X) ≅ D+(ν^*(X)[A]) ⋙ R+(globalSectionsFunctor A X) :=
  have : (comparisonLowerStar A X).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (comparisonAdjunction A X)
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso (comparisonAdjunction A X).derivedPlus.unit)
      R+(Etale.sectionsFunctor A X) ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D+(ν^*(X)[A])
      (Functor.rightDerivedFunctorPlusCompIso (comparisonLowerStar A X)
        (Etale.sectionsFunctor A X)).symm

/-- Blueprint `lem-weil-pbc-comparison-global-cohomology`: the isomorphism
`H^q(X_ét, M) ≅ H^q(X_proét, ν^* M)` between the étale cohomology of an étale sheaf `M` and the
pro-étale cohomology of its comparison pullback, obtained from
`rightDerivedFunctorPlusEtaleSectionsFunctorIso` by taking cohomology in degree `q`. -/
noncomputable def rightDerivedEtaleSectionsFunctorObjIso (M : Sheaf X.smallEtaleTopology A)
    (q : ℕ) :
    ((Etale.sectionsFunctor A X).rightDerived q).obj M ≅
      ((globalSectionsFunctor A X).rightDerived q).obj ((comparisonUpperStar A X).obj M) :=
  ((Etale.sectionsFunctor A X).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      q).symm.app M ≪≫
    (DerivedCategory.Plus.homologyFunctor A q).mapIso
      ((rightDerivedFunctorPlusEtaleSectionsFunctorIso A X).app _ ≪≫
        R+(globalSectionsFunctor A X).mapIso
          (((comparisonUpperStar A X).mapDerivedCategoryPlusSingleFunctor 0).app M)) ≪≫
    ((globalSectionsFunctor A X).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      q).app _

end AlgebraicGeometry.ProEtale
