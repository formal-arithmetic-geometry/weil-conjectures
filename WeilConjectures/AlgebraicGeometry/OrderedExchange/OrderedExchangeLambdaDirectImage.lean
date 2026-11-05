/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits
import all WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientData
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Restriction commutes with the direct-image/derived-limit comparisons

All five comparisons in `lambda_directImageRlimIso` are adjunction mates of exact descents of
ordinary identity-component squares. Transposing along the constant-diagram and tower-pullback
adjunctions reduces the equation to a cube of such squares, which is checked on complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.Functor

section SquareIsoQ

variable {𝒜 ℬ ℬ' ℰ : Type*} [Category 𝒜] [Category ℬ] [Category ℬ'] [Category ℰ]
  [Abelian 𝒜] [Abelian ℬ] [Abelian ℬ'] [Abelian ℰ] [HasDerivedCategory 𝒜]
  [HasDerivedCategory ℬ] [HasDerivedCategory ℬ'] [HasDerivedCategory ℰ]
  {F₁ : 𝒜 ⥤ ℬ} {F₂ : ℬ ⥤ ℰ} {G₁ : 𝒜 ⥤ ℬ'} {G₂ : ℬ' ⥤ ℰ}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

end SquareIsoQ

section Cube

variable {C₀ C₁ C₂ C₃ C₄ C₅ C₆ C₇ : Type*} [Category C₀] [Category C₁] [Category C₂]
  [Category C₃] [Category C₄] [Category C₅] [Category C₆] [Category C₇]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄] [Abelian C₅] [Abelian C₆]
  [Abelian C₇] [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃] [HasDerivedCategory C₄] [HasDerivedCategory C₅]
  [HasDerivedCategory C₆] [HasDerivedCategory C₇]
  {rV : C₀ ⥤ C₁} {δV : C₁ ⥤ C₂} {πc : C₂ ⥤ C₃} {κV : C₀ ⥤ C₄} {ρV : C₄ ⥤ C₂}
  {πt : C₄ ⥤ C₅} {ρU : C₅ ⥤ C₃} {pd : C₀ ⥤ C₆} {κU : C₆ ⥤ C₅} {pc : C₁ ⥤ C₇}
  {δU : C₇ ⥤ C₃} {rU : C₆ ⥤ C₇}
  [rV.Additive] [PreservesFiniteLimits rV] [PreservesFiniteColimits rV]
  [δV.Additive] [PreservesFiniteLimits δV] [PreservesFiniteColimits δV]
  [πc.Additive] [PreservesFiniteLimits πc] [PreservesFiniteColimits πc]
  [κV.Additive] [PreservesFiniteLimits κV] [PreservesFiniteColimits κV]
  [ρV.Additive] [PreservesFiniteLimits ρV] [PreservesFiniteColimits ρV]
  [πt.Additive] [PreservesFiniteLimits πt] [PreservesFiniteColimits πt]
  [ρU.Additive] [PreservesFiniteLimits ρU] [PreservesFiniteColimits ρU]
  [pd.Additive] [PreservesFiniteLimits pd] [PreservesFiniteColimits pd]
  [κU.Additive] [PreservesFiniteLimits κU] [PreservesFiniteColimits κU]
  [pc.Additive] [PreservesFiniteLimits pc] [PreservesFiniteColimits pc]
  [δU.Additive] [PreservesFiniteLimits δU] [PreservesFiniteColimits δU]
  [rU.Additive] [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]

end Cube

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.OrderedExchange
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U V : Scheme.{t}} (u : U ⟶ V)

set_option quotPrecheck false
local notation "aD" => proEtaleRingDerivedAdjunction u (AdicCoefficientDatum.completedRing d V)
  (AdicCoefficientDatum.completedRing d U) (AdicCoefficientDatum.integralRingIso d u)
local notation "aC" => proEtaleRingDerivedAdjunction u (exchangeConstantRing V A)
  (exchangeConstantRing U A) (exchangeConstantIso u A)
local notation "tC" => exchangeTowerAdjunction u (exchangeConstantRing V A)
  (exchangeConstantRing U A) (exchangeConstantIso u A)
local notation "αV" => (Functor.mapDerivedCategorySquareIso (ordinaryScalarDiagonal d V).symm).hom
local notation "αU" => (Functor.mapDerivedCategorySquareIso (ordinaryScalarDiagonal d U).symm).hom
local notation "βR" => (Functor.mapDerivedCategorySquareIso (exchangeModuleResPull d u).symm).hom

end AlgebraicGeometry.Scheme.OrderedExchange
