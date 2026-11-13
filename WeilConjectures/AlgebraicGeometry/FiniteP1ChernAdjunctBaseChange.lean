/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctMate
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange

/-! # Exchange for the normalized projective-line Chern adjunct
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace

/-- The adjuncts of two specified Kummer classes commute with exchange. -/
theorem ordinaryFiniteP1_chern_adjunct_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (c' : ordinaryFiniteUnit A (ProjectiveLine S') ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S'))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA S
      ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
        hS.map (ProjectiveLine S ↘ S).appTop.hom) c)
    (hc' : ordinaryFiniteP1ChernSpec A N hA S'
      ((map_natCast (ProjectiveLine S' ↘ S').appTop.hom N) ▸
        hS'.map (ProjectiveLine S' ↘ S').appTop.hom) c') :
    (ordinaryFinitePullback A f).map (ordinaryFiniteP1ChernPushforward A N hA S c) ≫
        ordinaryFiniteP1Exchange A f
          ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteShiftedLinePullback A N hA t
            (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
            ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
              hS.map (ProjectiveLine S ↘ S).appTop.hom)).hom =
      (ordinaryFiniteUnitPullback A f).hom ≫
        ordinaryFiniteP1ChernPushforward A N hA S' c' := by
  apply ordinaryFiniteP1_chern_adjunct_of_map_baseChange A N hN hA t f hS hS' c c'
  exact ordinaryFiniteP1_chern_map_baseChange A N hN hA t f hS hS' c c' hc hc'

end AlgebraicGeometry.Etale
