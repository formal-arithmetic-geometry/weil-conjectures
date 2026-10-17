/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralResidueTensorModel
import Sheaf.Paper.IntegralResidueDerivedMonoidal
import Sheaf.Paper.IntegralResidueOrdinaryMonoidal
import Sheaf.Paper.IntegralResidueTensorPresentation

/-! Descent of the tensor-route computation from resolving representatives.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-descent)

The statement isolates the naturality and essential-surjectivity step. -/

@[expose] public section

universe v u u₁ u₂

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Descent of a natural tensor-route equality from K-flat pullback models.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-descent)

Proof obligation. Choose a K-flat pullback model and an isomorphism from its
homotopy image to the given derived object.  Naturality of the two route maps
transports the equality along that isomorphism; cancel its invertible image.
This theorem contains only the descent step and no tensor-presentation
calculation. -/
theorem integralResidue_tensorRoute_descend {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (f)^*⟦integralCoeff ℓ E⟧.Monoidal)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat)
    (hRoute : ∀ P : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ),
      ((f)^*⟦integralCoeff ℓ E⟧).kFlatMap P →
      (letI := residueExchangePullMonoidal ℓ E f m hFlat
       (residueExchangeUpperStar (integralCoeff ℓ E) f).map
            ((residueExchangeTensorIso ℓ E Y).hom.app (DerivedCategory.Qh.obj P)) ≫
          Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
            (DerivedCategory.Qh.obj P) (residueExchangeCoefficient ℓ E Y) ≫
          residueExchangeTensorModelTarget ℓ E f P =
        residueExchangeTensorModelMap ℓ E f P)) :
    ∀ P : HomotopyCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) Y)) (.up ℤ),
      letI := residueExchangePullMonoidal ℓ E f m hFlat
      (residueExchangeUpperStar (integralCoeff ℓ E) f).map
            ((residueExchangeTensorIso ℓ E Y).hom.app (DerivedCategory.Qh.obj P)) ≫
          Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
            (DerivedCategory.Qh.obj P) (residueExchangeCoefficient ℓ E Y) ≫
          residueExchangeTensorModelTarget ℓ E f P =
        residueExchangeTensorModelMap ℓ E f P := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
