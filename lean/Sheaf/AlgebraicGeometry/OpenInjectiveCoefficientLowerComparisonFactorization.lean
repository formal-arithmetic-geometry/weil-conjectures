module
public import Sheaf.AlgebraicGeometry.BaseChangeStalkTransition
public import Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
@[expose] public section
universe u
namespace AlgebraicGeometry.Etale

/-- The derived mate calculation identifies the open injective coefficient map with the
ordinary base-change map on the coefficient `j_*J`. Source: Stacks Project, Tag 0F07,
closed-open lower comparison.
(blueprint: lem-sbc-open-injective-coefficient-lower-comparison-factorization)

Proof: rewrite `Etale.baseChange` by
`Etale.baseChange_eq_derivedBaseChangeMapPlus`, and then use the mate computation
`Adjunction.derivedPlus_mateEquiv_app_fac` for the pullback comparison.  On the
single complex containing `j_*J`, the exact pullback comparison is
`mapDerivedCategoryPlusSingleFunctor 0`; composing it with the counit of
`j^* ⊣ j_*` is the displayed final factor.  Naturality of the derived unit and
the two adjunction triangle identities then identify the resulting mate with
the left-hand composite.  Applying the homology functor preserves this equality.
-/
theorem open_injective_coefficient_lower_comparison_factorization
    (Λ : Type (u + 1)) [CommRing Λ]
    {Y T V W : Scheme.{u}}
    (e : Y ⟶ T) (j : V ⟶ T) (eV : W ⟶ V) (a : W ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j]
    (wa : a ≫ e = eV ≫ j) (sq : IsPullback eV a j e)
    (n : ℤ) (J : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective J] :
    ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) a).derivedPlus.unit.app
        (D+((e)^*[ModuleCat.{u + 1} Λ]).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
              (((j)_*[ModuleCat.{u + 1} Λ]).obj J))) ≫
        R+((a)_*[ModuleCat.{u + 1} Λ]).map
          ((upperStarPlusComp (ModuleCat.{u + 1} Λ) a e).inv.app _ ≫
            eqToHom (by rw [wa]) ≫
            (upperStarPlusComp (ModuleCat.{u + 1} Λ) eV j).hom.app _ ≫
            D+((eV)^*[ModuleCat.{u + 1} Λ]).map
              ((((j)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
                (((j)_*[ModuleCat.{u + 1} Λ]).obj J) ≫
                (DerivedCategory.Plus.singleFunctor _ 0).map
                  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).counit.app J))))) =
      (DerivedCategory.Plus.homologyFunctor _ n).map
        (D+((e)^*[ModuleCat.{u + 1} Λ]).map
            (CategoryTheory.Functor.rightDerivedPlusSingleUnit
              ((j)_*[ModuleCat.{u + 1} Λ]) J) ≫
          (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj J))  := by
  sorry
end AlgebraicGeometry.Etale
