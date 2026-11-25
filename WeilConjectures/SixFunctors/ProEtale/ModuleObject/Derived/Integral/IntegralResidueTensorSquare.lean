/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Integral.IntegralResidueTensorPresentation
public import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueTensorGeometry

/-! # Tensor coherence of the residue pull square

## References

- Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.5.9(3), Remark 6.8.15.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralResidueTensorSquare
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

attribute [local instance 2000] residueExchangeIntegralDerivedMonoidal

/-- The canonical residue tensor square, with a constructed derived monoidal structure. -/
theorem integralResidue_tensorSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ m : (residueExchangeUpperStar (integralCoeff ℓ E) f).Monoidal,
      letI := m
      ∃ (tY : residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y ≅
            tensorRight (residueExchangeCoefficient ℓ E Y))
        (tX : residueExchangeReduction ℓ E X ⋙ residueExchangeRestriction ℓ E X ≅
            tensorRight ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj
              (residueExchangeCoefficient ℓ E Y))),
        ∀ M : residueExchangeDerived (integralCoeff ℓ E) Y,
          (residueExchangeUpperStar (integralCoeff ℓ E) f).map (tY.hom.app M) ≫
              Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
                M (residueExchangeCoefficient ℓ E Y) =
            (residueExchangeRestrictPullIso ℓ E f).hom.app
                ((residueExchangeReduction ℓ E Y).obj M) ≫
              (residueExchangeRestriction ℓ E X).map
                (((residueExchangePullComparisons ℓ E).pull f).inv.app M) ≫
              tX.hom.app ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) := by
  unfold residueExchangeIntegralDerivedMonoidal
  obtain ⟨hFlat, ht⟩ := integralResidue_tensorGeometry ℓ E f
  exact ⟨residueExchangePullMonoidal ℓ E f
      (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat,
    residueExchangeTensorIso ℓ E Y, residueExchangeTensorPullIso ℓ E f, ht⟩

end AlgebraicGeometry.ProEtale.CondensedRing
