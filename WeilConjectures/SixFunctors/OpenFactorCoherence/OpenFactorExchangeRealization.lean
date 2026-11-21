/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorCoherenceData
public import WeilConjectures.SixFunctors.OpenExchangeRoos.OpenExchangeRoosRestriction

/-! # Open-factor data in the fixed coefficient presentation

## References

* Bhatt–Scholze, *The pro-étale topology for schemes*, 3.4.10, 6.5.5 and 6.5.8
* [Stacks, Tag 099N]
* [Stacks, Tag 09BN]
* [Stacks, Tag 0GL1]
* [Stacks, Tag 0D6D]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport
namespace WeilConjectures.OpenFactorCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Transport the strict completed exchange and its restricted unit square. -/
theorem openFactorExchangeRealization
    (F : FiniteFieldDatum.{u}) (hl : l ≠ F.p)
    (U' U X' X : Over (Spec (.of F.k)))
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (h : X' ⟶ X)
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (sq : OpenImmersionSquare a.left j'.left j.left h.left)
    (od : Open l E j.left) (od' : Open l E j'.left)
    (hb : OpenExchangeRoos.Assertion l E a.left j'.left j.left h.left
      (qc := OpenExchangeRoos.finiteOpenQC F U X j) sq) :
    ∃ (oh : Pull l E h.left) (oa : Pull l E a.left) (b : OrdinaryExchange l E sq)
      (r : integralDerivedPullback.{u, u} l E h.left ⋙ star l E j'.left ≅
        star l E j.left ⋙ integralDerivedPullback.{u, u} l E a.left),
      (∀ K : D l E X.left,
        (star l E j'.left).map ((oh.unit l E).app K) ≫ r.hom.app K =
          (theta l E sq).hom.app K ≫ (oa.unit l E).app ((star l E j.left).obj K)) ∧
      (∀ K : D l E U.left, sfIntegralConstructible l E U.left K →
        (star l E j'.left).map (beta l E b oh oa od' K) ≫
            od'.restrictionIso.hom.app ((integralDerivedPullback.{u, u} l E a.left).obj K) =
          r.hom.app ((J l E j.left).obj K) ≫
            (integralDerivedPullback.{u, u} l E a.left).map (od.restrictionIso.hom.app K)) ∧
      (∀ K : D l E U.left, sfIntegralConstructible l E U.left K →
        Function.Injective
          (fun v : (integralDerivedPullback.{u, u} l E h.left).obj
              ((J l E j.left).obj K) ⟶
              (J l E j'.left).obj ((integralDerivedPullback.{u, u} l E a.left).obj K) ↦
            (oh.unit l E).app ((J l E j.left).obj K) ≫ v)) := by sorry

end WeilConjectures.OpenFactorCoherence
