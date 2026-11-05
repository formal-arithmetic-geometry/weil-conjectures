/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityCoefficientWeilReduction
public import WeilConjectures.WeilSheaf.SmoothPurityEquivariantLift

/-! # Ordinary reduction preserves the transported Weil equation -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The actual transition between two finite reductions preserves equivariance for the
actual geometric pullback/reduction comparisons. The scheme endomorphism need not be
linear over a chosen base field. -/
theorem isWeilEquivariant_derivedReductionStep (g : X ⟶ X) (n : ℕ)
    {K L : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X))}
    (φK : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj K ⟶ K)
    (φL : L((g)^*⟦Profinite.padicIntegersRingObj ℓ E⟧).obj L ⟶ L)
    (s : (purityIntegralReduction X ℓ E (n + 1)).obj K ⟶
      (purityIntegralReduction X ℓ E (n + 1)).obj L)
    (hs : IsWeilEquivariant L((g)^*⟦Profinite.integersModPowRingObj ℓ E (n + 1)⟧)
      (transportWeilDatum _ (integersModPowReductionUpperStarIso ℓ E (n + 1) g) φK)
      (transportWeilDatum _ (integersModPowReductionUpperStarIso ℓ E (n + 1) g) φL) s) :
    IsWeilEquivariant L((g)^*⟦Profinite.integersModPowRingObj ℓ E n⟧)
      (transportWeilDatum _ (integersModPowReductionUpperStarIso ℓ E n g) φK)
      (transportWeilDatum _ (integersModPowReductionUpperStarIso ℓ E n g) φL)
      (derivedReductionStep n s) := by
  exact isWeilEquivariant_coefficientReduction
    (Profinite.padicIntegersRingObjToIntegersModPow ℓ E (n + 1))
    (Profinite.integersModPowRingObjTransition ℓ E n)
    (Profinite.padicIntegersRingObjToIntegersModPow ℓ E n) g
    (Profinite.padicIntegersRingObjToIntegersModPow_comp_integersModPowRingObjTransition ℓ E n)
    φK φL s hs

end AlgebraicGeometry.ProEtale
