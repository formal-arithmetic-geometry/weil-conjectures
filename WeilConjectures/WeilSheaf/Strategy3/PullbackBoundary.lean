module

public import WeilConjectures.WeilSheaf.Strategy3.Pullback

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u
open CategoryTheory MonoidalCategory MonObj

namespace AlgebraicGeometry.ProEtale.Strategy3

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

lemma lowerStar_eq : lowerStar Λ f = CondensedRing.lowerStar Λ f := by rfl

lemma upperStar_eq : upperStar Λ f = CondensedRing.upperStar Λ f := by rfl

lemma linearLowerStar_eq : linearLowerStar Λ f = CondensedRing.linearLowerStar Λ f := by rfl

lemma comapPullbackHomCompIso_eq :
    comapPullbackHomCompIso Λ f = CondensedRing.comapPullbackHomCompIso Λ f := by rfl

lemma upperStarLowerStarAdjunction_eq :
    upperStarLowerStarAdjunction Λ f = CondensedRing.upperStarLowerStarAdjunction Λ f := by
  unfold upperStarLowerStarAdjunction CondensedRing.upperStarLowerStarAdjunction
  rw [comapPullbackHomCompIso_eq]

end AlgebraicGeometry.ProEtale.Strategy3
