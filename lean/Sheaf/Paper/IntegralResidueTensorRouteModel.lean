/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralResidueTensorModel
import Sheaf.Paper.IntegralResidueTensorRouteGeneric

/-! Computation of the tensor-route in the residue tensor square.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-model)

The target is the explicit ordinary homotopy tensor model. -/

@[expose] public section

set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

attribute [local semireducible] residueExchangeUpperStar

/-- Compute the tensor-route against the ordinary homotopy tensor model.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-model)

Proof. Use the counit normalization of the fixed derived tensor presentation.
Move the coefficient single-functor comparison through the tensor comparison by
naturality. Compatibility of the derived tensor comparison with symmetry moves
the fixed coefficient to the first tensor factor. Its defining counit identity
then replaces the derived tensor comparison by Qh of the ordinary tensor
comparison. Naturality of the exact-pullback counit moves the homotopy
single-tensor comparison through it. The resulting composite is precisely
the displayed tensor model map. Every equality is an identity of natural
transformations, so no flatness of the residue coefficient or of P is required. -/
theorem integralResidue_tensorRoute_model {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    letI := residueExchangePullMonoidal ℓ E f
      (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat
    let M := DerivedCategory.Qh.obj P
    (residueExchangeUpperStar (integralCoeff ℓ E) f).map
          ((residueExchangeTensorIso ℓ E Y).hom.app M) ≫
        Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
          M (residueExchangeCoefficient ℓ E Y) ≫
        residueExchangeTensorModelTarget ℓ E f P =
      residueExchangeTensorModelMap ℓ E f P := by
  unfold residueExchangeUpperStar
  letI := residueExchangeOrdinaryPullMonoidal ℓ E f
  letI := hFlat
  letI := residueExchangeTensorCounit_isLeftDerivedFunctor ℓ E Y
  have h := residue_tensor_route_model_generic (f)^*⟦integralCoeff ℓ E⟧
    (residueExchangePullMonoidal ℓ E f (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat)
    (residueExchangePullMonoidal_δ ℓ E f (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat)
    (residueExchangeOrdinaryCoefficient ℓ E Y)
    (residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y)
    (residueExchangeTensorCounit ℓ E Y) (residueExchangeTensorIso ℓ E Y)
    (residueExchangeTensorIso_eq ℓ E Y) (residue_ordinary_pull_braiding ℓ E f) P
    (residueExchangeTensorModelTarget ℓ E f P) (residueExchangeTensorModelTarget_eq ℓ E f P)
    (residueExchangeTensorModelMap ℓ E f P) (residueExchangeTensorModelMap_eq ℓ E f P)
  exact h

end AlgebraicGeometry.ProEtale.CondensedRing
