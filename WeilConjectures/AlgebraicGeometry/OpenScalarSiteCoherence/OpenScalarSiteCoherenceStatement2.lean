/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients

/-! # Open extension/scalar/site coherence (current ordinary model)

Source: Stacks Project, `sites-cohomology.tex`, Tags 06YQ, 0GL1 and 09AF;
blueprint `lem-sp-open-scalar-site-coherence`.

The scalar functors and their normalization are those of the current ordinary
coefficient interfaces, fixed by the actual exact restriction adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.OpenScalarSiteCoherence

/-- The canonical etale scalar/open mate of the published restriction square.
The ordinary scalar unit sends a section to its tensor with 1, so the adjunction
normalization retains each extension summand and tensors its section with b.
Source: Stacks 03EL, 0E8I, 0GL1 (blueprint: lem-sp-open-scalar-site-coherence). -/
def etaleScalarOpen
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        CoefficientScalarRepresentatives.extension X.smallEtaleTopology φ ≅
      CoefficientScalarRepresentatives.extension U.smallEtaleTopology φ ⋙
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).comp
      (CoefficientScalarRepresentatives.adjunction X.smallEtaleTopology φ)).leftAdjointUniq
    (((CoefficientScalarRepresentatives.adjunction U.smallEtaleTopology φ).comp
      (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) j)).ofNatIsoRight
      (Functor.mapDerivedCategorySquareIso
        (Etale.upperStarRestrictScalarsIso φ j).symm))

/-- The same canonical scalar/open mate on the ordinary pro-etale site.
It is fixed by the scalar and open adjunctions, not by an arbitrary isomorphism.
Source: Stacks 03EL, 0E8I, 0GL1 (blueprint: lem-sp-open-scalar-site-coherence). -/
def proEtaleScalarOpen
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        CoefficientScalarRepresentatives.extension (Scheme.ProEt.topology X) φ ≅
      CoefficientScalarRepresentatives.extension (Scheme.ProEt.topology U) φ ⋙
        (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  ((ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).comp
      (CoefficientScalarRepresentatives.adjunction (Scheme.ProEt.topology X) φ)).leftAdjointUniq
    (((CoefficientScalarRepresentatives.adjunction (Scheme.ProEt.topology U) φ).comp
      (ProEtale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) j)).ofNatIsoRight
      (Functor.mapDerivedCategorySquareIso (ProEtale.upperStarRestrictScalarsIso φ j).symm))

/-- The published identity-open comparison, descended by exact localization.
Source: Stacks 09AF (blueprint: lem-sp-open-scalar-site-coherence). -/
def extensionId (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :=
  Functor.mapDerivedCategoryNatIso
    (openImmersionLowerShriekIdIso (ModuleCat.{u + 1} A) X) ≪≫
      Functor.mapDerivedCategoryIdIso _

end AlgebraicGeometry.ProEtale.OpenScalarSiteCoherence
