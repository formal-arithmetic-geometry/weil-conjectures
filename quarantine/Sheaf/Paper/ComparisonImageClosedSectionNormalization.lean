/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.Paper.CartierClassAgreement
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import Sheaf.Paper.ClosedSectionCompactOrigin

/-! # Closed-section normalization for comparison-image coefficients

The coefficient on the pro-etale site is the comparison inverse image of the etale
constant. This is the presentation used by the supported cup and divisor classes.
Source: blueprint, thm-pur-rank-one-thom.proof.md, Step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurityFiniteSetting

set_option allowUnsafeReducibility true in
attribute [local reducible] functorialCupSheaves functorialCupCategory functorialCupAbelian
  functorialCupHasDerived functorialCupSingle functorialCupComparisonFunctor
  functorialCupSource functorialCupTwist


attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategorySingleFunctor

variable (P : PurityFiniteSetting.{u}) {B X : Scheme.{u}}
  (f : X ⟶ B) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [HasCompactification f] (s : B ⟶ X) [IsClosedImmersion s]
  [QuasiCompact s.openComplement.ι]
  [PreservesFiniteColimits (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) s)]
  [HasCompactification (s ≫ f)] (hs : s ≫ f = 𝟙 B)

/-- Canonical closed-section construction used in source normalization.
Source: rank-one Thom proof Step 1
(blueprint: lem-pur-comparison-image-closed-section-normalization). -/
def closedSectionUe (T : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
      (DerivedCategory.Plus.singleFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj (P.constantEtale T)

/-- Canonical closed-section construction used in source normalization.
Source: rank-one Thom proof Step 1
(blueprint: lem-pur-comparison-image-closed-section-normalization). -/
def closedSectionSe :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
      (DerivedCategory.Plus.singleFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj
        (P.functorialCupSource false s)

/-- Canonical closed-section construction used in source normalization.
Source: rank-one Thom proof Step 1
(blueprint: lem-pur-comparison-image-closed-section-normalization). -/
def closedSectionSp :
    DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) :=
      (DerivedCategory.Plus.singleFunctor
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
        (P.functorialCupSource true s)

/-- Canonical closed-section construction used in source normalization.
Source: rank-one Thom proof Step 1
(blueprint: lem-pur-comparison-image-closed-section-normalization). -/
def closedSectionChi (T : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
      (closedSectionUe P T).obj ≅
      (DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
        (P.constant T) :=
      ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategorySingleFunctor
        0).app
      (P.constantEtale T)

attribute [local irreducible] closedSectionChi

/-- Canonical closed-section construction used in source normalization.
Source: rank-one Thom proof Step 1
(blueprint: lem-pur-comparison-image-closed-section-normalization). -/
def closedSectionEpsilon :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj
      (closedSectionSe P s).obj ≅ (closedSectionSp P s).obj :=
      ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategorySingleFunctor
      0).app
      (P.functorialCupSource false s) ≪≫
    (DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)) 0).mapIso
      (P.functorialCupComparisonSource_existsUnique s).choose

attribute [local irreducible] closedSectionEpsilon

/-- Canonical closed-section construction used in source normalization.
Source: rank-one Thom proof Step 1
(blueprint: lem-pur-comparison-image-closed-section-normalization). -/
def closedSectionOrigin (T : Scheme.{u}) :
    (ProEtale.DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} P.Coefficient) T).FullSubcategory :=
      (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) T).obj
      ((closedSectionUe P) T)

/-- Canonical closed-section construction used in source normalization.
Source: rank-one Thom proof Step 1
(blueprint: lem-pur-comparison-image-closed-section-normalization). -/
def closedSectionIp :
        (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) s).obj
          ((closedSectionOrigin P) B).obj ≅ (closedSectionSp P s).obj :=
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      s).mapIso ((closedSectionChi P) B) ≪≫
    (ProEtale.rightDerivedLowerShriekIsoOfIsProper
      (ModuleCat.{u + 1} P.Coefficient) s).app _ ≪≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      s).rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
    ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      s).mapDerivedCategorySingleFunctor 0).app (P.constant B)

attribute [local irreducible] closedSectionIp

/-- Canonical closed-section construction used in source normalization.
Source: rank-one Thom proof Step 1
(blueprint: lem-pur-comparison-image-closed-section-normalization). -/
def closedSectionIe :
        (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) s).obj
          ((closedSectionUe P) B) ≅ (closedSectionSe P s) :=
      DerivedCategory.Plus.ι.preimageIso
      ((Etale.rightDerivedLowerShriekPlusCompatibility
        (ModuleCat.{u + 1} P.Coefficient) s).app _ ≪≫
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} P.Coefficient) s).app _ ≪≫
      (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        s).rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        s).mapDerivedCategorySingleFunctor 0).app (P.constantEtale B))

attribute [local irreducible] closedSectionIe

/-- Canonical closed-section construction used in source normalization.
Source: rank-one Thom proof Step 1
(blueprint: lem-pur-comparison-image-closed-section-normalization). -/
def closedSectionSigmap :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).obj
      (closedSectionSp P s).obj ≅
      (DerivedCategory.singleFunctor
        (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
        (P.constant B) :=
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).mapIso
      ((closedSectionIp P s)).symm ≪≫
    (ProEtale.originCompositionAmbient P.Coefficient s f).app
      ((closedSectionOrigin P) B) ≪≫
    (ProEtale.rightDerivedLowerShriekCongr (ModuleCat.{u + 1} P.Coefficient)
      hs).app _ ≪≫
    (ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) B).ι.mapIso
      ((ProEtale.originCompactSupportId P.Coefficient B).app ((closedSectionOrigin P) B)) ≪≫
    (closedSectionChi P) B

attribute [local irreducible] closedSectionSigmap

/-- Canonical closed-section construction used in source normalization.
Source: rank-one Thom proof Step 1
(blueprint: lem-pur-comparison-image-closed-section-normalization). -/
def closedSectionSigmae :
    (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) f).obj
      (closedSectionSe P s) ≅ closedSectionUe P B :=
      (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) f).mapIso
      ((closedSectionIe P s)).symm ≪≫
    (Etale.rightDerivedLowerShriekPlusCompIso P.Coefficient s f).app
      ((closedSectionUe P) B) ≪≫
    (Etale.rightDerivedLowerShriekPlusCongr P.Coefficient hs).app _ ≪≫
    (Etale.rightDerivedLowerShriekPlusId P.Coefficient B).app _

attribute [local irreducible] closedSectionSigmae

/-- Canonical closed-section construction used in source normalization.
Source: rank-one Thom proof Step 1
(blueprint: lem-pur-comparison-image-closed-section-normalization). -/
def closedSectionBeta :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj
      ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) f).obj
        (closedSectionSe P s)).obj ≅
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).obj
        (closedSectionSp P s).obj :=
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
      ((Etale.rightDerivedLowerShriekPlusCompatibility
        (ModuleCat.{u + 1} P.Coefficient) f).app ((closedSectionSe P s))) ≪≫
    ((compactSupportSiteComparison P.Coefficient
      (HasCompactification.compactification f)).app ((closedSectionSe P s))).symm ≪≫
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).mapIso
      ((closedSectionEpsilon P s))

attribute [local irreducible] closedSectionBeta

/-- The closed-section compact-source comparison, for comparison-image constants.

Source: current blueprint, sec-smooth-purity/sk-prop-an,
thm-pur-rank-one-thom.proof.md, Step 1; the source equation of
lem-pur-closed-section-compact-origin.
(blueprint: lem-pur-comparison-image-closed-section-normalization).

Proof: apply closed_section_compact_origin at the standing compactification of f.
Its pro-etale coefficient is the standard constant sheaf, whereas Sp below uses
comparison inverse image. Let q_B be comparisonUpperStarUnitIso on B and let q_s
be s_*q_B, both embedded in degree zero. Naturality of the proper and exact-derived
comparisons identifies the generic closed isomorphism with Ip followed by q_s.
The supported comparison in that lemma is epsilon followed by q_s: both preserve
constant restriction, so use uniqueness in functorialCupComparisonSource_existsUnique
and the normalized counit mate. Its constant comparison is chi followed by q_B.
The etale source is Sigmae, since the self compactification comparison is the identity.
The pro-etale source is Fp(q_s inverse), followed by Sigmap and q_B. Indeed expand
its definition, use the preceding closed-isomorphism equality, and remove the self
candidate comparison by fully faithful descent and the etale self-comparison law.
Substitute these identities into the generic source equation. Functoriality cancels
Fp(q_s) with Fp(q_s inverse); cancellation of q_B gives exactly the equation below.
No property of a Cartier class or of a target map occurs in this calculation. -/
theorem comparisonImage_closed_section_normalization (P : PurityFiniteSetting.{u})
    {B X : Scheme.{u}} (b : B ⟶ Spec (.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (f : X ⟶ B) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f] (s : B ⟶ X) [IsClosedImmersion s]
    [QuasiCompact s.openComplement.ι]
    [PreservesFiniteColimits (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) s)]
    [HasCompactification (s ≫ f)] (hs : s ≫ f = 𝟙 B) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map (closedSectionSigmae P f s hs).hom) ≫
      (closedSectionChi P B).hom =
      (closedSectionBeta P f s).hom ≫ (closedSectionSigmap P f s hs).hom := by
  sorry

end WeilConjectures.PurityFiniteSetting
