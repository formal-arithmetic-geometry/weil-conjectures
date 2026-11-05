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

/-- Type-only control for the failed direct comparison; it asserts no equation. -/
def finiteComparisonBoundaryType : Prop :=
  upperStarFiniteCoefficientModEquivalenceIso g T =
    ProEtale.upperStarFiniteCoefficientModEquivalenceIso g T

end AlgebraicGeometry.ProEtale.Strategy3
