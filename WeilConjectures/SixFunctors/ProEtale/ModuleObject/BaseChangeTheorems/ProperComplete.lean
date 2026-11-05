/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedAdicComplete
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeResidueExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.SmoothPadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.RegularEndDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CountableProducts
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama
public import WeilConjectures.Tactic.ExactModProofs

/-!

# Proper base change for derived complete integral complexes

Let `t : P ⟶ Q` be proper and `g : Q' ⟶ Q` a morphism along which the derived pullbacks
`Lg^*` and `Lg'^*` preserve countable products (for instance closed immersions,
`ProEtale.CondensedRing.preservesLimitsOfShape_leftDerivedUpperStar_of_isCompl`). For a bounded
below complex `R` of `𝒪_{E,P}`-modules which is derived `ℓ`-adically complete
(`CategoryTheory.IsDerivedAdicComplete`) and whose first derived reduction `R ⊗ᴸ 𝔽_E` is of
étale origin, the base change morphism `Lg^* Rt_* R ⟶ Rt'_* Lg'^* R` is an isomorphism
(`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper_of_isDerivedAdicComplete`).

This is blueprint `sk-prop-pbc-complete` in the case where the completed inverse images agree
with the inverse images. The proof: both sides of the base change morphism are derived complete
(`Rt_*` is a right adjoint, and `Lg^*`, `Lg'^*` preserve the products), hence so is its cone
`C`. The first derived reduction of the base change morphism is the pro-étale base change
morphism with coefficients `𝔽_E` at `R ⊗ᴸ 𝔽_E`
(`ProEtale.CondensedRing.nonempty_arrowIso_derivedReduction_map_exchangeRight`), invertible by
proper base change for torsion coefficients
(`ProEtale.isIso_derivedBaseChangeMap_app_of_isProper`). So `C ⊗ᴸ 𝔽_E = 0`, `ℓ` acts invertibly on
`C` (`ProEtale.isIso_zsmul_id_of_isZero_derivedReduction`) and `C = 0` by derived Nakayama
(`CategoryTheory.IsDerivedAdicComplete.isZero_of_isIso_zsmul_id`).

-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)
  {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

end AlgebraicGeometry.ProEtale.CondensedRing
