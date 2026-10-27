/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.EtaleCoordinateTraceData
/-! The pre-pullback equality of the two coordinate Kunneth routes. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.CoordinateTrace
variable (A : Type (u + 1)) [CommRing A]

/-- The two direct-image coordinate Kunneth routes agree before applying pullback.
Source: the mate calculation in the proof of the coordinate Kunneth factorization.
Proof: expand both routes by the ordered projection, exchange, comparison, and
direct comparison mate equations, then use naturality of the tensor comparison.
(blueprint: lem-sfb-etale-coordinate-kunneth-route-equality). -/
theorem coordinateKunnethFactorization_route_eq [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (L : DerivedCategoryModule A Y)
    (M : DerivedCategoryModule A X) :
    (orderedProjectionIso A f ((push A f).obj M) ((pull A f).obj L)).hom ≫
        (push A f).map (comparison A f L M).inv ≫
          (directComparison A f).hom.app _ =
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app M).app
          ((push A f).obj ((pull A f).obj L)) ≫
        (push A f).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
              (exchange1 A f ((pull A f).obj L)).hom ≫
            (orderedProjectionIso A (pullback.fst f f) M
              ((pull A (pullback.snd f f)).obj ((pull A f).obj L))).hom) := by
  sorry
end AlgebraicGeometry.Etale.CoordinateTrace
