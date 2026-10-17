/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralResidueTensorModel
import Sheaf.Paper.IntegralResidueDerivedMonoidal
import Sheaf.Paper.IntegralResidueOrdinaryMonoidal
import Sheaf.Paper.IntegralResidueTensorPresentation
import Sheaf.Paper.IntegralResidueTensorRouteKFlat
import Sheaf.Paper.IntegralResidueTensorRouteDescent

/-! Computation of the tensor-route in the residue tensor square.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-model)

The target is the explicit ordinary homotopy tensor model. -/

@[expose] public section

universe v u u₁ u₂

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The normalized tensor-route equation for an explicit ordinary monoidal structure.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-transport)

This strictly generalizes the target by taking the ordinary monoidal structure as
an explicit parameter. Its proof is the transport of the generic tensor-route
factorization through the residue exchange interface and the canonical tensor
presentation. -/
theorem integralResidue_tensorRoute_model_transport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (f)^*⟦integralCoeff ℓ E⟧.Monoidal)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ)) :
    letI := residueExchangePullMonoidal ℓ E f m hFlat
    (residueExchangeUpperStar (integralCoeff ℓ E) f).map
          ((residueExchangeTensorIso ℓ E Y).hom.app (DerivedCategory.Qh.obj P)) ≫
        Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
          (DerivedCategory.Qh.obj P) (residueExchangeCoefficient ℓ E Y) ≫
        residueExchangeTensorModelTarget ℓ E f P =
      residueExchangeTensorModelMap ℓ E f P := by
  apply integralResidue_tensorRoute_descend ℓ E f m hFlat
  intro P hP
  exact integralResidue_tensorRoute_kFlat ℓ E f m hFlat P hP

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
  simpa only [] using integralResidue_tensorRoute_model_transport ℓ E f
    (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat P


end AlgebraicGeometry.ProEtale.CondensedRing
