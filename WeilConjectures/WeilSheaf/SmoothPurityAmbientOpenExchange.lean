/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.CondensedModelBaseChange
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeConjugate
public import WeilConjectures.CategoryTheory.DerivedCategory.ExchangeLeftAdjoint
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoSymm

/-! # Normalization of the exact open exchange used by geometric descent -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [IsOpenImmersion g] [IsOpenImmersion g']

/-- The descent open exchange is the inverse of the canonical left exchange. -/
lemma purityOpenImmersionLowerShriekUpperStarBaseChangeIso_inv
    (sq : IsPullback g' f' f g) :
    (openImmersionLowerShriekUpperStarBaseChangeIso Λ sq).inv =
      Adjunction.exchangeLeft
        (openImmersionLowerShriekUpperStarAdjunction Λ g)
        (openImmersionLowerShriekUpperStarAdjunction Λ g')
        (upperStarSquareComparison Λ sq.toCommSq) := by
  unfold openImmersionLowerShriekUpperStarBaseChangeIso
  rw [Iso.symm_inv, conjugateIsoEquiv_symm_apply_hom]
  apply (conjugateEquiv
    ((openImmersionLowerShriekUpperStarAdjunction Λ g).comp
      (upperStarLowerStarAdjunction Λ f))
    ((upperStarLowerStarAdjunction Λ f').comp
      (openImmersionLowerShriekUpperStarAdjunction Λ g'))).injective
  rw [Equiv.apply_symm_apply, Adjunction.conjugateEquiv_exchangeLeft]
  rfl

/-- Deriving the normalized open square preserves its adjunction mate. -/
lemma purityOpenImmersionLowerShriekMapDerivedCategoryBaseChangeIso_inv
    (sq : IsPullback g' f' f g) [WeaklyEtale f] [WeaklyEtale f'] :
    (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ sq).inv =
      Adjunction.exchangeLeft
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ g)
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ g')
        (Functor.mapDerivedCategorySquareIso (upperStarSquareComparison Λ sq.toCommSq)) := by
  have he := purityOpenImmersionLowerShriekUpperStarBaseChangeIso_inv Λ sq
  have : IsIso (Adjunction.exchangeLeft
      (openImmersionLowerShriekUpperStarAdjunction Λ g)
      (openImmersionLowerShriekUpperStarAdjunction Λ g')
      (upperStarSquareComparison Λ sq.toCommSq)) := by
    rw [← he]
    infer_instance
  have he' : asIso (Adjunction.exchangeLeft
      (openImmersionLowerShriekUpperStarAdjunction Λ g)
      (openImmersionLowerShriekUpperStarAdjunction Λ g')
      (upperStarSquareComparison Λ sq.toCommSq)) =
      (openImmersionLowerShriekUpperStarBaseChangeIso Λ sq).symm := by
    apply Iso.ext
    exact he.symm
  rw [derivedOpenImmersionLowerShriekUpperStarAdjunction,
    derivedOpenImmersionLowerShriekUpperStarAdjunction,
    Adjunction.exchangeLeft_mapDerivedCategoryAdjunction, he',
    Functor.mapDerivedCategorySquareIso_symm]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
