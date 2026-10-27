/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J6
-/
module

public import Sheaf.Paper.SectionCompactSourceMaps

/-! # The site-comparison square for the actual compact-support exchange

Source: Stacks Project, Tags 099R and 09AF; blueprint
thm-cbc-finite-level-proetale, proper/open factorization of transported exchange.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SectionCompactSource

/-- The canonical compact-support comparison intertwines the actual compactification
exchanges on every bounded-below etale complex. No supported constant, section, or
normalization of a section source enters this assertion.
Source: Stacks Tags 099R and 09AF; thm-cbc-finite-level-proetale, proper/open
transport calculation (blueprint: lem-pur-compact-support-site-exchange-square).

Proof: factor the compactification as the open immersion j followed by the proper p.
Properness of p and its pullback gives qcqs. The counit-normalized proper comparison
intertwines the two proper mates by compactSupportProperFactor, applied to j_!K.
The open comparison intertwines the two inverse extension-by-zero exchanges by
fixSiteOpenExchange, valid for arbitrary finite A and arbitrary base change.
Move the open comparison through the proper exchange by naturality and paste these
two equations. Functoriality combines the target factors. The resulting comparisons
are precisely compactSupportSiteComparisonPlus and fixedComparisonPullbackPlus.
To identify the pro-etale D+ exchange with proExchange, apply the fully faithful
bounded-below inclusion: its definition is the preimage of the ambient proper/open
mate with the exact-to-left-derived and right-derived inclusion comparisons.
The exact-derived adjunction unit and counit formulas identify the proper factors;
the termwise open-base-change comparison identifies the open factors. Naturality
cancels the intervening inverse comparison pairs. The etale factor is its formalism
mate by derivedPlusFormalism_pfBaseChange and the formalism's open base-change
identification. Thus the pasted equation is the displayed equality for the specified
maps. This argument uses no Noetherian, finite-type, quasi-compactness or separation
condition on the new base; zero complexes and empty schemes are included. -/
theorem compact_support_site_exchange_square
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X' X B' B : Scheme.{u}} {v : X' ⟶ X} {h' : X' ⟶ B'}
    {h : X ⟶ B} {g : B' ⟶ B} (sq : IsPullback v h' h g) (c : Compactification h)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.map
        ((ProEtale.compactSupportSiteComparisonPlus A c).hom.app K) ≫
      proExchange A sq c
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj K) =
    (ProEtale.fixedComparisonPullbackPlus A g).inv.app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} A) c).obj K) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) B').mapDerivedCategoryPlus.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c).app K) ≫
      (ProEtale.compactSupportSiteComparisonPlus A (c.ofIsPullback sq)).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus.obj K) ≫
      (ProEtale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map
          ((ProEtale.fixedComparisonPullbackPlus A v).hom.app K) := by sorry

end AlgebraicGeometry.SectionCompactSource
