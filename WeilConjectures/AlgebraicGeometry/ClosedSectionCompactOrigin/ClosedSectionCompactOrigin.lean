/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.SupportedConstantNormalization.SupportedConstantExchangeNormalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ClosedSectionCompactOrigin.ClosedSectionCompactOriginData
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport

/-! # Naturality of the compact-support site comparison

The comparison between the étale and pro-étale compactly supported direct images along a
compactification is natural in the bounded-below étale complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.ProEtale
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.singleFunctorCompRightDerivedFunctorIso
  CategoryTheory.Functor.mapDerivedCategorySingleFunctor
  AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
  AlgebraicGeometry.ProEtale.rightDerivedLowerShriekIsoOfIsProper

namespace AlgebraicGeometry.ClosedSectionCompactOrigin
variable (P : WeilConjectures.PurityFiniteSetting.{u})

local instance transportCoefficientFinite : Finite P.Coefficient :=
  letI : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  Finite.of_equiv P.Ring Equiv.ulift.symm
attribute [local irreducible] WeilConjectures.PurityFiniteSetting.Coefficient
  WeilConjectures.PurityFiniteSetting.Ring

set_option maxRecDepth 2048
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] constantComparison supportedComparison etaleClosedIso proClosedIso
  compactComparison compactSupportSiteComparison originCompositionAmbient originCompactSupportId
  towerCandidateComparison proSigma etaleSigma etaleTau proTau targetComparison
  originComposition

/-- The compact-support site comparison `compactComparison P c` is natural in the bounded-below
étale complex. -/
lemma compactComparison_naturality {X Y : Scheme.{u}} {v : X ⟶ Y}
    (c : Compactification v)
    {L M : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))} (t : L ⟶ M) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
          ((Etale.rightDerivedLowerShriekOfCompactificationPlus
            (ModuleCat.{u + 1} P.Coefficient) c).map t)) ≫
        (compactComparison P c M).hom =
      (compactComparison P c L).hom ≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} P.Coefficient) c).map
            ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
              (DerivedCategory.Plus.ι.map t)) := by
  simpa only [compactExchangeTransportComparison, compactComparison, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Functor.comp_map,
    Category.id_comp, Category.comp_id, Category.assoc] using
    (compactExchangeTransportComparison P.Coefficient c).hom.naturality t

end AlgebraicGeometry.ClosedSectionCompactOrigin
