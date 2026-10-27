/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.AlgebraicGeometry.EtaleCoordinateTraceData
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
/-! The right coordinate route is the canonical Kunneth map after composition. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.CoordinateTrace
variable (A : Type (u + 1)) [CommRing A]

/-- The projection/exchange route identifies with the canonical Kunneth map after
composing `R p₁_*` and `R f_*`.  This is the second mate calculation in the
coordinate interchange argument.
Source: the coordinate interchange calculation in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-geo-p1-adjunction/`.
(blueprint: lem-sfb-etale-coordinate-kunneth-right-route-comp-kunneth).
-/
theorem coordinateKunneth_rightRoute_comp_kunneth
    [Finite A] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (L : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X) :
    (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app M).app
          ((push A f).obj ((pull A f).obj L)) ≫
        (push A f).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
              (exchange1 A f ((pull A f).obj L)).hom ≫
            (orderedProjectionIso A (pullback.fst f f) M
              ((pull A (pullback.snd f f)).obj ((pull A f).obj L))).hom)) ≫
        (rightDerivedLowerStarCompIsoOfComp (ModuleCat.{u + 1} A)
          (pullback.fst f f) f (pullback.fst f f ≫ f) rfl).hom.app _ =
      kunnethMap (ModuleCat.{u + 1} A) (pullback.fst f f) (pullback.snd f f)
        f f (pullback.fst f f ≫ f) rfl (pullback.condition (f := f) (g := f)).symm
        M ((pull A f).obj L) := by
  sorry
end AlgebraicGeometry.Etale.CoordinateTrace
