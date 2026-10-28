/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.EtaleCoordinateTraceData
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
/-! The pre-composition mate calculation for the left coordinate route. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.CoordinateTrace
variable (A : Type (u + 1)) [CommRing A]

/-- The left coordinate route agrees with the projection/base-change factorization before
composing with the canonical direct-image compositor.
Source: the coordinate interchange calculation in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-geo-p1-adjunction/`.
The proof expands the ordered projection, comparison mate and direct compositor, then uses
naturality of the derived tensor comparison and the mate equations for proper exchange.
(blueprint: new-sfb-etale-coordinate-kunneth-left-route-precomp). -/
theorem coordinateKunneth_leftRoute_precomp
    [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (L : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X) :
    (orderedProjectionIso A f ((push A f).obj M) ((pull A f).obj L)).hom ≫
        (push A f).map (comparison A f L M).inv ≫
          (directComparison A f).hom.app _ =
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app M).app
          ((push A f).obj ((pull A f).obj L)) ≫
        (push A f).map
          (tensorBaseChangeMap (ModuleCat.{u + 1} A) (pullback.fst f f)
            (pullback.snd f f) f f
            (pullback.condition (f := f) (g := f)) M ((pull A f).obj L)) := by
  sorry
end AlgebraicGeometry.Etale.CoordinateTrace
