/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullSquareData
import WeilConjectures.CategoryTheory.Integral.IntegralResidueMatePasting
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueRestrictPullComp

/-! # Composition of the canonical residue pull mates

## References

- Bhatt--Scholze, *The pro-étale topology for schemes*, Remark 6.8.15.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance instEssentiallySmallProfinite_integralResiduePullSquareComp
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The inverse mates satisfy the composition coherence equation. -/
theorem integralResidue_pullSquare_comp :
      ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
        (K : residueExchangeDerived (integralCoeff ℓ E) Z),
        (residueExchangeReduction ℓ E X).map
            ((residueExchangeUpperStarComp (integralCoeff ℓ E) f g).hom.app K) ≫
          (residueExchangePullHom ℓ E f).app
            ((residueExchangeUpperStar (integralCoeff ℓ E) g).obj K) ≫
          (residueExchangeUpperStar
            (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
            ((residueExchangePullHom ℓ E g).app K) =
        (residueExchangePullHom ℓ E (f ≫ g)).app K ≫
          (residueExchangeUpperStarComp
            (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f g).hom.app
            ((residueExchangeReduction ℓ E Z).obj K) := by
  intro X Y Z f g K
  unfold residueExchangePullHom
  exact inverseMate_pasting
    (residueExchangeReductionAdjunction ℓ E Z)
    (residueExchangeReductionAdjunction ℓ E Y)
    (residueExchangeReductionAdjunction ℓ E X)
    (residueExchangeRestrictPullIso ℓ E g).hom
    (residueExchangeRestrictPullIso ℓ E f).hom
    (residueExchangeRestrictPullIso ℓ E (f ≫ g)).hom
    (residueExchangeUpperStarComp (integralCoeff ℓ E) f g).hom
    (residueExchangeUpperStarComp
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f g).hom
    (residueExchangeRestrictPullIso_comp ℓ E f g) K

end AlgebraicGeometry.ProEtale.CondensedRing
