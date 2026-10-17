/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralResidueTensorModel
import Sheaf.Paper.IntegralResidueDerivedMonoidal
import Sheaf.Paper.IntegralResidueOrdinaryMonoidal
import Sheaf.Paper.IntegralResidueTensorPresentation

/-! Tensor-route computation on the resolving class.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-kflat)

This is the component calculation before descent from K-flat representatives. -/

@[expose] public section

universe v u u₁ u₂

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Tensor-route equality on representatives whose ordinary pullback is K-flat.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-kflat)

Proof obligation. Expand the derived tensor comparison on an F-K-flat representative,
move the coefficient presentation through the symmetry isomorphism, and use the
counit identity of the canonical restricted tensor presentation.  The remaining
ordinary comparison is the defining tensor-model map.  This is the resolving-class
component of the route calculation; descent to arbitrary P is a separate theorem. -/
theorem integralResidue_tensorRoute_kFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (f)^*⟦integralCoeff ℓ E⟧.Monoidal)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat)
    (P : HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ))
    (hP : ((f)^*⟦integralCoeff ℓ E⟧).kFlatMap P) :
    letI := residueExchangePullMonoidal ℓ E f m hFlat
    (residueExchangeUpperStar (integralCoeff ℓ E) f).map
          ((residueExchangeTensorIso ℓ E Y).hom.app (DerivedCategory.Qh.obj P)) ≫
        Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
          (DerivedCategory.Qh.obj P) (residueExchangeCoefficient ℓ E Y) ≫
        residueExchangeTensorModelTarget ℓ E f P =
      residueExchangeTensorModelMap ℓ E f P := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
