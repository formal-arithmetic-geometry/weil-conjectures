module

public import WeilConjectures.WeilSheaf.Strategy3.FinitePullback

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.Strategy3
open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  [DiscreteTopology T] [Finite T] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- Compare just the source functor, before comparing isomorphisms. -/
lemma finiteComparisonSource_eq :
    Strategy3.upperStar (Profinite.continuousMapRingObj T) g ⋙ (finiteCoefficientModEquivalence X T).functor =
      CondensedRing.upperStar (Profinite.continuousMapRingObj T) g ⋙
        (ProEtale.finiteCoefficientModEquivalence X T).functor := by rfl

/-- Compare just the target functor, before comparing isomorphisms. -/
lemma finiteComparisonTarget_eq :
    (finiteCoefficientModEquivalence Y T).functor ⋙
        (g)^*[ModuleCat.{u + 1} (coeffType.{u} T)] =
      (ProEtale.finiteCoefficientModEquivalence Y T).functor ⋙
        (g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)] := by rfl

/-- Explicit endpoint transport avoids silently identifying two whole iso types. -/
noncomputable def finiteComparisonTransport :
    CondensedRing.upperStar (Profinite.continuousMapRingObj T) g ⋙
        (ProEtale.finiteCoefficientModEquivalence X T).functor ≅
      (ProEtale.finiteCoefficientModEquivalence Y T).functor ⋙
        (g)^*[ModuleCat.{u + 1} (ULift.{u + 1} T)] :=
  (eqToIso (finiteComparisonSource_eq T g)).symm ≪≫
    upperStarFiniteCoefficientModEquivalenceIso g T ≪≫
      eqToIso (finiteComparisonTarget_eq T g)

lemma finiteComparisonTransport_eq :
    finiteComparisonTransport T g = ProEtale.upperStarFiniteCoefficientModEquivalenceIso g T := by
  rfl

end AlgebraicGeometry.ProEtale.Strategy3
