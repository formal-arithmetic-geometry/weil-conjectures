module

public import WeilConjectures.WeilSheaf.SmoothPurityOpenExchangeNormalization
public import WeilConjectures.WeilSheaf.SmoothPurityOpenAdjunctionTransport
public import WeilConjectures.WeilSheaf.SmoothPurityOpenReductionAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.PushforwardDataRings
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs

/-! # The integral compactification exchange along an open immersion -/

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
  [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

/-- The generic open identification is the existing integral identification. -/
lemma purity_integralOpenIso_eq (j : X ⟶ Y) [IsOpenImmersion j.left] :
    (padicIntegersPushforwardData ℓ k E).purityOpenIso
        (isIsoRefinementPushforward_padicIntegersPushforwardData ℓ k E) j =
      boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers ℓ E j := by
  rfl

variable {j : X ⟶ Y} {g : Y' ⟶ Y} {j' : X' ⟶ Y'} {g' : X' ⟶ X}
  [IsOpenImmersion j.left] [IsOpenImmersion j'.left]

/-- The actual integral compact-support exchange, through the canonical open isos. -/
theorem purity_integralLowerShriekBaseChange_comp_open (sq : IsPullback g' j' j g) :
    boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq ≫
      Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g')
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers ℓ E j').hom ≫
      boundedConstructibleOpenImmersionLowerShriekBaseChange
        (Profinite.padicIntegersRingObj ℓ E) ℓ sq.toCommSq =
    Functor.whiskerRight
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers ℓ E j).hom
      (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g) := by
  rw [boundedConstructibleLowerShriekBaseChange_padicIntegers_eq_pushforwardData]
  simpa only [purity_integralOpenIso_eq] using
    (padicIntegersPushforwardData ℓ k E).purity_lowerShriekBaseChange_comp_open
      (isIsoRefinementPushforward_padicIntegersPushforwardData ℓ k E) sq

/-- The integral open adjunction exchange is extension exchange transported through
the canonical compact-support identifications. -/
theorem purity_integralOpenExchange_comp_open (sq : CommSq g' j' j g) :
    Adjunction.exchangeLeft (purityIntegralOpenPullAdjunction ℓ E j)
        (purityIntegralOpenPullAdjunction ℓ E j')
        (boundedConstructiblePullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) ℓ
          sq.flip) ≫
      Functor.whiskerRight
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers ℓ E j).hom
        (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g) =
    Functor.whiskerLeft (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g')
        (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers ℓ E j').hom ≫
      boundedConstructibleOpenImmersionLowerShriekBaseChange
        (Profinite.padicIntegersRingObj ℓ E) ℓ sq := by
  rw [purityIntegralOpenPullAdjunction, purityIntegralOpenPullAdjunction,
    boundedConstructibleUpperShriekIsoUpperStar_padicIntegers,
    boundedConstructibleUpperShriekIsoUpperStar_padicIntegers,
    Adjunction.purity_ofNatIsoRight_conjugate, Adjunction.purity_ofNatIsoRight_conjugate,
    boundedConstructibleOpenImmersionLowerShriekBaseChange_eq_exchangeLeft]
  exact Adjunction.purity_exchangeLeft_ofNatIsoLeft _ _ _ _ _

/-- The actual integral compactification exchange is inverse to the open adjunction
exchange. This is the integral outer boundary needed by the reduction cube. -/
theorem purity_integralOpenExchange_eq_inv_baseChange (sq : IsPullback g' j' j g) :
    Adjunction.exchangeLeft (purityIntegralOpenPullAdjunction ℓ E j)
        (purityIntegralOpenPullAdjunction ℓ E j')
        (boundedConstructiblePullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E) ℓ
          sq.toCommSq.flip) =
      inv (boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq) := by
  have := isIso_boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq
  symm
  apply IsIso.inv_eq_of_hom_inv_id
  apply (cancel_mono (Functor.whiskerRight
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicIntegers ℓ E j).hom
    (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ g))).mp
  rw [Category.assoc, purity_integralOpenExchange_comp_open,
    purity_integralLowerShriekBaseChange_comp_open, Category.id_comp]

end AlgebraicGeometry.ProEtale.CondensedRing
