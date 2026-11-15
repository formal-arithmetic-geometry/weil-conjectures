/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageKanRepresentative
public import WeilConjectures.AlgebraicGeometry.EtaleSectionsFpqcDescent
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonComposition
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonIdentity
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalRestriction
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.RightDerivedExactComposite
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
public import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-! # Geometric comparison on the existing small site models

These are the original inclusion and geometric adjunction transported by AsSmall.

## References

* Stacks Project, Tags 099R, 00WX and 00X6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The etale site model in a universe containing the coefficient ring
(Stacks, Tags 00VC and 099R). -/
abbrev smallModelComparisonEtaleSite (X : Scheme.{u}) := AsSmall.{max v (u + 1)} X.Etale

/-- The original etale topology transported by the model equivalence
(Stacks, Tags 00VC and 099R). -/
abbrev smallModelComparisonEtaleTopology (X : Scheme.{u}) :=
  (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).inducedTopology
    X.smallEtaleTopology

/-- The original inclusion transported to the two coefficient-sized models
(Stacks, Tag 099R). -/
abbrev smallModelComparisonInclusion (X : Scheme.{u}) :
    smallModelComparisonEtaleSite.{u, v} X ⥤ coefficientProEtaleSiteModel.{u, v} X :=
  AsSmall.down ⋙ toProEt X ⋙ AsSmall.up

/-- The transported inclusion is continuous, retaining the original covers
(Stacks, Tag 099R). -/
@[instance]
theorem smallModelComparisonInclusion_isContinuous (X : Scheme.{u}) :
    (smallModelComparisonInclusion.{u, v} X).IsContinuous
      (smallModelComparisonEtaleTopology.{u, v} X)
      (coefficientProEtaleModelTopology.{u, v} X) := by
  have := Functor.isContinuous_comp (toProEt X) AsSmall.up
    X.smallEtaleTopology (ProEt.topology X) (coefficientProEtaleModelTopology.{u, v} X)
  exact Functor.isContinuous_comp AsSmall.down (toProEt X ⋙ AsSmall.up)
    (smallModelComparisonEtaleTopology.{u, v} X) X.smallEtaleTopology
    (coefficientProEtaleModelTopology.{u, v} X)

/-- The comparison inverse image on the existing small models (Stacks, Tag 099R). -/
abbrev smallModelComparisonPullback (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (smallModelComparisonInclusion.{u, v} X) (Type (max v (u + 1)))
    (smallModelComparisonEtaleTopology.{u, v} X) (coefficientProEtaleModelTopology.{u, v} X)

/-- The comparison direct image on the same models (Stacks, Tag 099R). -/
abbrev smallModelComparisonPushforward (X : Scheme.{u}) :=
  (smallModelComparisonInclusion.{u, v} X).sheafPushforwardContinuous (Type (max v (u + 1)))
    (smallModelComparisonEtaleTopology.{u, v} X) (coefficientProEtaleModelTopology.{u, v} X)

/-- The geometric comparison on the existing small models (Stacks, Tag 099R). -/
abbrev smallModelProEtaleComparison (X : Scheme.{u}) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallModelComparisonInclusion.{u, v} X) (Type (max v (u + 1)))
    (smallModelComparisonEtaleTopology.{u, v} X) (coefficientProEtaleModelTopology.{u, v} X)

/-- Comparison remains left exact after transporting along the model equivalences
(Stacks, Tags 099R and 00X6). -/
@[instance]
theorem smallModelComparisonPullback_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (smallModelComparisonPullback.{u, v} X) := by
  have : (AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale).IsRightAdjoint :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isRightAdjoint_inverse
  have : (AsSmall.up : X.ProEt ⥤ coefficientProEtaleSiteModel.{u, v} X).IsRightAdjoint :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).symm.isRightAdjoint_inverse
  have : RepresentablyFlat (smallModelComparisonInclusion.{u, v} X) :=
    inferInstanceAs (RepresentablyFlat
      ((AsSmall.down : smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale) ⋙
        toProEt X ⋙ AsSmall.up))
  exact Functor.sheafPullbackConstruction.instPreservesFiniteLimitsSheafSheafPullback
    (smallModelComparisonInclusion.{u, v} X) (Type (max v (u + 1)))
    (smallModelComparisonEtaleTopology.{u, v} X) (coefficientProEtaleModelTopology.{u, v} X)

end AlgebraicGeometry.Scheme
