/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralResidueTensorModel
public import Sheaf.Paper.IntegralResidueTensorPullPresentation

/-! Computation of the scalar-route in the residue tensor square.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-scalar-route-model)

The target is the explicit ordinary homotopy tensor model. -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Compute the scalar-route against the ordinary homotopy tensor model.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-scalar-route-model)

Proof. Expand the canonical restriction/pullback square using the exact
pullback identifications. The scalar comparison is the inverse mate of this
square. Its counit identity cancels the scalar-extension comparison against the
extension counit that defines the tensor presentation on X. The ordinary
restriction/pullback square and the regular-module unit comparison identify its
coefficient with the inverse image of the coefficient on Y. On ordinary balanced
tensor presentations both remaining maps send s tensor m to s tensor f*(m):
precompose with the balanced coequalizer epimorphism to verify the equality.
Apply the homotopy quotient and Qh; the exact-pullback counit and the defining
left-derived comparison identities give the stated formula. The extension
counit is retained as a map, so P and the residue coefficient need not be flat. -/
theorem integralResidue_scalarRoute_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    letI := residueExchangePullMonoidal ℓ E f
      (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat
    let M := DerivedCategory.Qh.obj P
    (residueExchangeRestrictPullIso ℓ E f).hom.app
          ((residueExchangeReduction ℓ E Y).obj M) ≫
        (residueExchangeRestriction ℓ E X).map
          (((residueExchangePullComparisons ℓ E).pull f).inv.app M) ≫
        (residueExchangeTensorPullIso ℓ E f).hom.app
          ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) ≫
        residueExchangeTensorModelTarget ℓ E f P =
      residueExchangeTensorModelMap ℓ E f P := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
