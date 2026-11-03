/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantProjectionMap
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.CategoryTheory.Site.SiteDerivedTensorRestriction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ProEtaleCoefficients.RestrictedKFlatTensorIdentification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
public import WeilConjectures.CategoryTheory.SixFunctors.UnaryWhiskeringOfProduct
public import WeilConjectures.Algebra.Homology.FlatSingleDerivedNormalization.FlatSingleDerivedNormalization
public import WeilConjectures.Algebra.Homology.Derived.DerivedScalarExtensionCounitShift
public import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalars
public import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.FieldRestrictionExteriorProduct
import WeilConjectures.AlgebraicGeometry.ScalarChangeAdjunctions
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompExact
import WeilConjectures.Algebra.Homology.BifunctorSingleComparison
import WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MateCounit
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Etale-to-point exchange and scalar-action counits

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 07A4, 07A6, 0D6D,
0D6E and 0B56; the third paragraph of the current blueprint proof of
lem-pur-ordinary-kunneth-finite-ring (blueprint: lem-pur-etale-point-scalar-exchange). The
scalar counits are written in their normalized tensor coordinates. Their
representative equation is included explicitly: on a flat-term K-flat resolution
it is the class of x tensor beta mapping to beta g(x). Thus the tensor actions
below denote the restricted scalar-adjunction counits, rather than extra choices
of actions. The comparison of right adjoints is fixed by the right-derived units.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v c d

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale.PointScalarExchange

section TensorCoordinates

variable {C : Type c} {D : Type d} [Category.{v} C] [Category.{v} D]
  [Abelian C] [Abelian D] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v} D]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

omit [IsGrothendieckAbelian.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C] in
end TensorCoordinates

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

-- Pin the coefficient universe before using the site's sheaf-composition instances.
local instance (φ : A →+* B) :
    PreservesLimits (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ) :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ).rightAdjoint_preservesLimits

local instance (φ : A →+* B) :
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).isLeftAdjoint

/-- The canonical ordinary constant-sheaf/scalar-restriction comparison.
Source: sheafification of the identity constant presheaf, Stacks 07A4
(blueprint: lem-pur-etale-point-scalar-exchange). -/
def constantExchange (T : Scheme.{u}) (φ : A →+* B) :
    ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ ⋙
        constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ≅
      constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} B) ⋙
        Sheaf.restrictScalars.{u + 1, u, u + 1} T.smallEtaleTopology φ :=
  letI : T.smallEtaleTopology.PreservesSheafification
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction T.smallEtaleTopology
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  (constantCommuteCompose T.smallEtaleTopology
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)).symm

set_option maxHeartbeats 400000 in
-- Normalize the tensor comparison and derived counit on complex representatives.
set_option maxHeartbeats 400000 in
-- Normalize the sheafification and scalar-adjunction comparisons.
private theorem constantExchange_eq (T : Scheme.{u}) (φ : A →+* B) :
    constantExchange T φ =
      (constantSheafCompSheafComposeIso T.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)).symm := by
  apply Iso.ext_inv
  ext M
  dsimp [constantExchange, constantCommuteCompose, constantSheafCompSheafComposeIso]
  rfl


private theorem sections_adjunct (T : Scheme.{u}) (φ : A →+* B)
    (Y : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    ((derivedConstantGlobalSectionsAdjunction
        (ModuleCat.{u + 1} A) T).homEquiv _ _).symm
        ((fieldRestrictionSectionsMap φ T).app Y) =
      (exchange T φ).hom.app
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} B) T).obj Y) ≫
        (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategory.map
          ((derivedConstantGlobalSectionsAdjunction (ModuleCat.{u + 1} B) T).counit.app Y) := by
  symm
  rw [Adjunction.homEquiv_counit]
  let eA := (constantSheaf T.smallEtaleTopology
    (ModuleCat.{u + 1} A)).leftDerivedFunctorIsoMapDerivedCategory
  have hε (X) : eA.hom.app _ ≫
      (derivedConstantSheafAdjunction (ModuleCat.{u + 1} A) T).counit.app X =
        (derivedConstantGlobalSectionsAdjunction (ModuleCat.{u + 1} A) T).counit.app X := by
    simp [derivedConstantSheafAdjunction, Adjunction.ofNatIsoLeft_counit, eA,
      derivedConstantGlobalSectionsAdjunction]
  have hm := mateEquiv_counit
    (derivedConstantSheafAdjunction (ModuleCat.{u + 1} B) T)
    (derivedConstantSheafAdjunction (ModuleCat.{u + 1} A) T)
    (Functor.mapDerivedCategorySquareIso
      (constantSheafCompSheafComposeIso T.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)).symm).hom Y
  change _ = _ ≫ _
  rw [← hε, eA.hom.naturality_assoc]
  dsimp only [fieldRestrictionSectionsMap]
  rw [hm]
  simp only [exchange, constantExchange_eq, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom, Functor.map_comp,
    Category.assoc, derivedConstantSheafAdjunction, Adjunction.ofNatIsoLeft_counit,
    derivedConstantGlobalSectionsAdjunction]
  rfl

set_option maxHeartbeats 1000000 in
-- Normalize the homotopy and derived adjunction comparisons in the mate equation.
set_option maxHeartbeats 1200000 in
-- Normalize the representative tensor square through the derived functor comparisons.
end AlgebraicGeometry.Etale.PointScalarExchange
