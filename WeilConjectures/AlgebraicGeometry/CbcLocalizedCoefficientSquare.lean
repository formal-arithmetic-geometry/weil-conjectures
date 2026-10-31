/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.NormalizedCoefficientFamilies
/-! Localization extension of the integral normalized square.
Source: rational transport proof step 16.
(blueprint: lem-cbc-localized-coefficient-square).
Proof: every raw rational object is an integral representative; scalar localization is
full and additive, so the integral equality transports to every object and morphism. -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

variable {X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}
  (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
  (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
  (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
  [IsNoetherian X'] [IsNoetherian Y']
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [iX' : Fact (∀ x : X', IsUnit (l : X'.presheaf.stalk x))]
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]


/-- Localization transports the integral normalized coefficient square to all raw
rational stage objects. (blueprint: lem-cbc-localized-coefficient-square).
Proof: every raw rational object is an integral representative, so destructing the
rational-stage wrapper reduces the assertion to the supplied integral equality. -/
theorem cbcLocalizedCoefficientSquare
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (H : CbcCompactSupportCoefficientFamily l Ω c)
    (H' : CbcCompactSupportCoefficientFamily l Ω c')
    (P : CbcCompletedPullCoefficientFamily l Ω g)
    (P' : CbcCompletedPullCoefficientFamily l Ω g')
    (τ : ∀ E : Padic.FiniteCoefficientFields l Ω, (H.family.base.Φ E ⋙ P.family.base.Φ E) ⟶
        (P'.family.base.Φ E ⋙ H'.family.base.Φ E))
    (_hτ : ∀ E : Padic.FiniteCoefficientFields l Ω,
      ∀ (K : pbcIntegralStage l Ω X E)
    (r : ℕ) (a : Fin r → PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (ha : Ideal.span (Set.range a) = (pbcStageDatum.{u} l Ω E).ideal)
    (hc : cbcCompleteProperty (pbcStageDatum.{u} l Ω E) X r a ha K.obj),
    ∃ (hs : PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        ((cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c.i c.isOpenImmersion ⋙
          (pbcStageDatum.{u} l Ω E).push c.g ⋙
            (pbcStageDatum.{u} l Ω E).completedPull g).obj K.obj))
      (ht : PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} l Ω E)
        (((pbcStageDatum.{u} l Ω E).completedPull g' ⋙
          cbcDerivedOpenShriek (pbcStageDatum.{u} l Ω E) c'.i c'.isOpenImmersion ⋙
            (pbcStageDatum.{u} l Ω E).push c'.g).obj K.obj)),
      HEq ((τ E).app ((pbcStageLocalization l Ω X E).obj K))
        ((pbcStageLocalization l Ω Y' E).map
          (ObjectProperty.homMk (X := ⟨_, hs⟩) (Y := ⟨_, ht⟩)
            (completedCompactSupportExchange (pbcStageDatum.{u} l Ω E)
              c c' gbar properSquare openSquare r a ha ⟨K.obj, hc⟩))))
    (hIntegral : ∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
      (K : pbcIntegralStage l Ω X E),
      ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).map
          ((τ E).app ((pbcStageLocalization l Ω X E).obj K)) ≫
        ((P'.family.base.comp H'.family.base).β h).hom.app
          ((pbcStageLocalization l Ω X E).obj K) =
      ((H.family.base.comp P.family.base).β h).hom.app
          ((pbcStageLocalization l Ω X E).obj K) ≫
        (τ F).app (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj
          ((pbcStageLocalization l Ω X E).obj K)))
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F)
    (K : pbcStageCategory l Ω X E) :
    ((pbcScalarSystem l Ω Y' dY'.out iY'.out).T h).map ((τ E).app K) ≫
        ((P'.family.base.comp H'.family.base).β h).hom.app K =
      ((H.family.base.comp P.family.base).β h).hom.app K ≫
        (τ F).app (((pbcScalarSystem l Ω X dX.out iX.out).T h).obj K)  := by
  rcases K with ⟨K⟩
  exact hIntegral h K

end AlgebraicGeometry.Scheme
