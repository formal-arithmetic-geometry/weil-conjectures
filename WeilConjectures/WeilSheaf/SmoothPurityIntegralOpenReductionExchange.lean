module

public import WeilConjectures.WeilSheaf.SmoothPurityIntegralOpenExchange
public import WeilConjectures.WeilSheaf.SmoothPurityOpenReductionExchange

/-! # The integral compact-support side of the open reduction cube -/

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

/-- Reduction commutes with the actual integral compact-support exchange and the
finite open-adjunction exchange. The finite compactification identification is separate. -/
theorem purity_squareCompatible_integralOpenEtaleReductionExchange
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left] (sq : IsPullback g' j' j g) :
    have := HasCompactification.of_over j
    have := HasCompactification.of_over j'
    have := isIso_boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq
    NatTrans.SquareCompatible
      (Functor.pasteSquareIso (etaleReductionUpperStarIso ℓ E n g')
        (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n j'))
      (Functor.pasteSquareIso (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n j)
        (etaleReductionUpperStarIso ℓ E n g))
      (inv (boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq))
      (Adjunction.exchangeLeft (purityEtaleOpenPullAdjunction ℓ E n j)
        (purityEtaleOpenPullAdjunction ℓ E n j')
        (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
          (⟨Over.left_comp_left_eq_of_comp_eq sq.toCommSq.flip.w⟩ :
            CommSq j'.left g'.left g.left j.left))) := by
  have := HasCompactification.of_over j
  have := HasCompactification.of_over j'
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq
  rw [← purity_integralOpenExchange_eq_inv_baseChange]
  exact purity_squareCompatible_openEtaleReductionExchange ℓ E n sq.toCommSq

end AlgebraicGeometry.ProEtale.CondensedRing
