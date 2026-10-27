/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J6
-/
module

public import Sheaf.Paper.SectionCompactSourceMaps
import Sheaf.Paper.CompactSupportSiteExchangeSquare

/-! # Compact-support transport of section source comparison

Source: blueprint rank-one Thom proof, Step 3; Stacks Tags 099R and 09AF.
(blueprint: lem-pur-section-source-pro-exchange-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SectionCompactSource

/-- The compact-support site comparison transports the section-source exchange to the
pro-etale exchange, before the scalar-source endpoint cancellation.
Source: blueprint rank-one Thom proof, Step 3; Stacks Tags 099R and 09AF.
Proof: apply the compact-support site-exchange square to `etaleSupported A s`.
Naturality of `proExchange` moves `compareSupported A s` through that square.
The normalized supported-constant comparison identifies the endpoint with `proBeta`;
naturality of the compact-support comparison moves `etaleBeta` through the remaining
comparison. The proof is independent of the section-source maps, constant pullback,
and the assumed etale source equation. It introduces no condition on the new base.
-/
theorem sourceComparison_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {B X B' X' : Scheme.{u}} {h : X ⟶ B} {h' : X' ⟶ B'}
    {v : X' ⟶ X} {g : B' ⟶ B} (sq : IsPullback v h' h g)
    (c : Compactification h) (s : B ⟶ X) (s' : B' ⟶ X')
    [IsClosedImmersion s] [IsClosedImmersion s']
    (sqS : ChosenCartesianSquare g s' s v) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.map
        (sourceComparison A c s) ≫ proExchange A sq c (proSupported A s) ≫
      (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map (proBeta A sqS) =
    (ProEtale.fixedComparisonPullbackPlus A g).inv.app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} A) c).obj (etaleSupported A s)) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) B').mapDerivedCategoryPlus.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c).app
            (etaleSupported A s) ≫
          (Etale.rightDerivedLowerShriekOfCompactificationPlus
            (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map (etaleBeta A sqS)) ≫
      sourceComparison A (c.ofIsPullback sq) s' := by sorry

end AlgebraicGeometry.SectionCompactSource
