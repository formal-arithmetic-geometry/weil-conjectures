/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullSquareData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullSquareIsIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullSquareComp

/-! # The scalar-adjunction normalization of the derived residue pull square

## References

- Bhatt--Scholze, *The pro-étale topology for schemes*, Remark 6.8.15.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralResiduePullSquare
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- The constructed scalar pull comparison is invertible and compatible with composition. -/
theorem integralResidue_pullSquare :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsIso (residueExchangePullHom ℓ E f)) ∧
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
  exact ⟨integralResidue_pullSquare_isIso ℓ E, integralResidue_pullSquare_comp ℓ E⟩

/-- The canonical coherent pull comparisons. The geometric theorem supplies only
invertibility and coherence; every component morphism was constructed beforehand. -/
@[irreducible] noncomputable def residueExchangePullComparisons :
    IntegralResiduePullComparisons.{u} ℓ E := by
  let {X Y : Scheme.{u}} (f : X ⟶ Y) : IsIso (residueExchangePullHom ℓ E f) :=
    (integralResidue_pullSquare ℓ E).1 f
  exact
    { pull := fun f ↦ asIso (residueExchangePullHom ℓ E f)
      comp := (integralResidue_pullSquare ℓ E).2 }

/-- Scalar-adjunction normalization for the canonical coherent comparison family. -/
theorem residueExchangePullComparisons_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : residueExchangeDerived
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) Y) :
    (residueExchangeReduction ℓ E X).map
        ((residueExchangeRestrictPullIso ℓ E f).hom.app N) ≫
      (residueExchangeReductionAdjunction ℓ E X).counit.app
        ((residueExchangeUpperStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).obj N) =
    ((residueExchangePullComparisons ℓ E).pull f).hom.app
        ((residueExchangeRestriction ℓ E Y).obj N) ≫
      (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
          ((residueExchangeReductionAdjunction ℓ E Y).counit.app N) := by
  unfold residueExchangePullComparisons
  exact residueExchangePullHom_counit ℓ E f N

end AlgebraicGeometry.ProEtale.CondensedRing
