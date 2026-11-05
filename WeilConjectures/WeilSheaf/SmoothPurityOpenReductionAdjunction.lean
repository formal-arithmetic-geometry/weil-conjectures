module

public import WeilConjectures.WeilSheaf.SmoothPurityOpenReductionMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionUpperShriekCanonical

/-! # The open compact-support reduction comparison is mated to pullback reduction -/

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
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (j : X ⟶ Y) [IsOpenImmersion j.left]

/-- The integral compact-support functor along an open immersion is left adjoint
to the actual bounded pullback. -/
noncomputable def purityIntegralOpenPullAdjunction :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E j ⊣
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ j :=
  (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E j).ofNatIsoRight
    (boundedConstructibleUpperShriekIsoUpperStar_padicIntegers ℓ E j)

/-- The finite compact-support functor in the same pullback coordinates. -/
noncomputable def purityEtaleOpenPullAdjunction :
    have := HasCompactification.of_over j
    Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
      j.left ⊣ L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
        j.left) :=
  have := HasCompactification.of_over j
  (Etale.rightDerivedUpperShriekAdjunction _ j.left).ofNatIsoRight
    (Etale.rightDerivedUpperShriekIsoOfIsOpenImmersion _ j.left ≪≫
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ j.left).symm)

/-- The canonical open compact-support coefficient comparison is the mate of the
canonical pullback comparison, including its concrete instance parameters. -/
theorem purity_isMateSquare_openEtaleReduction :
    have := HasCompactification.of_over j
    (purityIntegralOpenPullAdjunction ℓ E j).IsMateSquare
      (purityEtaleOpenPullAdjunction ℓ E n j)
      (etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n j)
      (etaleReductionUpperStarIso ℓ E n j) := by
  have := HasCompactification.of_over j
  apply Adjunction.isMateSquare_ofNatIsoRight_of_conjugate
  rw [Adjunction.isMateSquare_iff]
  exact mateEquiv_etaleReductionLowerShriekIsoOfIsOpenImmersion ℓ E n j

end AlgebraicGeometry.ProEtale.CondensedRing
