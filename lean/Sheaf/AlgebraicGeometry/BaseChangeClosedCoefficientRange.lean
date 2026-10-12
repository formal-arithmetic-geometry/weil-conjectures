/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeStalkTransition
import WeilConjectures.SixFunctors.OpenClosed.Stalk

/-! # Closed coefficient range comparison

Source: Stacks Project, Tag 0F07, closed–open part of the proof.
(blueprint: lem-sbc-closed-coefficient-range)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X S T : Scheme.{u}} (p : X ⟶ S) (g : T ⟶ S)
/-- A class that is a base-change image on the closed subscheme is an image after
mapping coefficients to the closed pushforward.

Source: Stacks Project, Tag 0F07, closed summand in condition (3).
(blueprint: lem-sbc-closed-coefficient-range)

Proof: the direct image along a closed immersion is exact on etale module sheaves,
and closed-immersion base change identifies e inverse image of i pushforward with
the corresponding closed pushforward on Y. Composition of derived direct images
therefore identifies the base-change map with coefficients i_* i^* F with the map
for the square over Z. Under these identifications the coefficient unit gives the
canonical target transition. Transport a source preimage across the source
identification to obtain the required preimage on T. This works also when Z is empty.
-/
theorem baseChange_closed_coefficient_mem_range (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
    {T' : Scheme.{u}} (f : T' ⟶ T)
    (ζ : baseChangeTargetStalk Λ p g q F x (Over.mk f))
    {Z : Scheme.{u}} (i : Z ⟶ T') [IsClosedImmersion i]
    (hζ : (baseChangeTargetStalkMap Λ p g q F x
      (Over.homMk i : Over.mk (i ≫ f) ⟶ Over.mk f)).hom ζ ∈
        Set.range (baseChangeStalkMap Λ p g q F x (Over.mk (i ≫ f))).hom) :
    ((X.uliftPointSmallEtale x).sheafFiber.map
      ((baseChangeTargetFunctor Λ (pullback.fst (f ≫ g) p)
        (pullback.snd (f ≫ g) p) q).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app
          (((f)^*[ModuleCat.{u + 1} Λ]).obj F)))).hom ζ ∈
      Set.range ((X.uliftPointSmallEtale x).sheafFiber.map
        (baseChangeHomologyMap Λ (IsPullback.of_hasPullback (f ≫ g) p) q
          (((i)_*[ModuleCat.{u + 1} Λ]).obj
            (((i)^*[ModuleCat.{u + 1} Λ]).obj
              (((f)^*[ModuleCat.{u + 1} Λ]).obj F))))).hom := by sorry

end AlgebraicGeometry.Etale
