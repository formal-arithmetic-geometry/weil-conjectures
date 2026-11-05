module

public import WeilConjectures.WeilSheaf.SmoothPurityOpenReductionAdjunction
public import WeilConjectures.WeilSheaf.SmoothPurityEtaleReductionPullback

/-! # Reduction commutes with the exchange of open compact-support adjunctions -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
  [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {j : X ⟶ Y} {g : Y' ⟶ Y} {j' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The canonical reduction pullback comparisons satisfy the coefficient cube in
the forward comparison coordinates consumed by adjunction exchange. -/
theorem purity_squareCompatible_etaleReductionPullback (sq : CommSq g' j' j g) :
    NatTrans.SquareCompatible
      (Functor.pasteSquareIso (etaleReductionUpperStarIso ℓ E n g)
        (etaleReductionUpperStarIso ℓ E n j'))
      (Functor.pasteSquareIso (etaleReductionUpperStarIso ℓ E n j)
        (etaleReductionUpperStarIso ℓ E n g'))
      (boundedConstructiblePullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) ℓ
        sq).hom
      (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
        (⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩ : CommSq g'.left j'.left j.left g.left)).hom := by
  apply NatTrans.SquareCompatible.of_inv_app
  intro K
  simpa only [Functor.pasteSquareIso_inv_app, Category.assoc] using
    purity_etaleReductionUpperStarIso_cube ℓ E n sq K

/-- Reduction commutes with the open extension exchange using the actual canonical
compact-support coefficient comparison. No orientation hypothesis occurs. -/
theorem purity_squareCompatible_openEtaleReductionExchange
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left] (sq : CommSq g' j' j g) :
    have := HasCompactification.of_over j
    have := HasCompactification.of_over j'
    NatTrans.SquareCompatible
      (Functor.pasteSquareIso (etaleReductionUpperStarIso ℓ E n g')
        (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n j'))
      (Functor.pasteSquareIso (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n j)
        (etaleReductionUpperStarIso ℓ E n g))
      (Adjunction.exchangeLeft (purityIntegralOpenPullAdjunction ℓ E j)
        (purityIntegralOpenPullAdjunction ℓ E j')
        (boundedConstructiblePullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) ℓ
          sq.flip))
      (Adjunction.exchangeLeft (purityEtaleOpenPullAdjunction ℓ E n j)
        (purityEtaleOpenPullAdjunction ℓ E n j')
        (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
          (⟨Over.left_comp_left_eq_of_comp_eq sq.flip.w⟩ :
            CommSq j'.left g'.left g.left j.left))) := by
  have := HasCompactification.of_over j
  have := HasCompactification.of_over j'
  exact NatTrans.SquareCompatible.exchangeLeft
    (purity_isMateSquare_openEtaleReduction ℓ E n j)
    (purity_isMateSquare_openEtaleReduction ℓ E n j')
    (purity_squareCompatible_etaleReductionPullback ℓ E n sq.flip)

end AlgebraicGeometry.ProEtale.CondensedRing
