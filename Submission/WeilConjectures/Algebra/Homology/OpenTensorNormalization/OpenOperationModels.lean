/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import all Submission.WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import all Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Submission.WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all Submission.WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import all Submission.WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import all Submission.WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all Submission.WeilConjectures.Algebra.Homology.CochainCompositeConstruction.CochainCompositeAlgebraic
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Submission.WeilConjectures.CategoryTheory.RingedToposRingData
import all Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Additive
import all Submission.WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.DerivedPullbackRepresentativeComputationSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Construction of open operation models -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

/- The adopted module-adjunction API equates the site hom universe and coefficient
universe. Here the site has objects in Type (u+1), homs in Type u, and coefficients
in Type (u+1). The following private helpers prove the same adjunction by its
sectionwise universal property at these universes; no public interface changes. -/
namespace GeneralizedRinged

open MonoidalCategory
open SheafOfModules.GeometricConstruction
open scoped ChangeOfRings
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option maxErrors 20

section
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : D ⥤ C) [F.IsContinuous K J]
  (L : Sheaf K (Type (u + 1)) ⥤ Sheaf J (Type (u + 1)))
  (adj : L ⊣ F.sheafPushforwardContinuous (Type (u + 1)) K J)

end
private noncomputable abbrev tensorFunctor
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S) :=
  CategoryTheory.CochainPullback.extensionFunctor (J := K) (A := A) (B := S) c

open SheafOfModules.GeometricConstruction
end GeneralizedRinged

open CategoryTheory.Functor MonoidalCategory

namespace SystemPresentation
open WeilConjectures WeilConjectures.SemilinearSections

set_option backward.isDefEq.respectTransparency false

end SystemPresentation

namespace SystemPresentation
open WeilConjectures WeilConjectures.SemilinearSections

set_option backward.isDefEq.respectTransparency false

end SystemPresentation

namespace SystemPresentation
open WeilConjectures WeilConjectures.SemilinearSections
set_option backward.isDefEq.respectTransparency false

end SystemPresentation

open SheafOfModules.CanonicalTensorPullbackOfUniverses CategoryTheory.Functor

namespace SiteRestriction
attribute [local irreducible] SheafOfModules.monoidalCategory
variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : D ⥤ C) [F.IsContinuous K J] [F.IsCocontinuous K J]

private abbrev ring (R : Sheaf J CommRingCat.{u + 1}) :=
  (F.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj R

private noncomputable def inverse (R : Sheaf J CommRingCat.{u + 1}) :
  AlgebraicInverseImage
      (F.sheafPushforwardContinuous (Type (u + 1)) K J) R
      ((F.sheafPushforwardContinuous CommRingCat.{u + 1} K J).obj R) where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h V x ↦ h (F.op.obj V) x
  ringMul := fun _ _ _ _ h V x ↦ h (F.op.obj V) x
  ringZero := fun _ _ h V x ↦ h (F.op.obj V) x
  ringOne := fun _ _ h V x ↦ h (F.op.obj V) x
  modules := SheafOfModules.pushforward.{u + 1} (F := F) (𝟙 _)
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h V x ↦ h (F.op.obj V) x
  moduleZero := fun _ _ _ h V x ↦ h (F.op.obj V) x
  moduleSMul := fun _ _ _ _ _ h V x ↦ h (F.op.obj V) x

end SiteRestriction

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

open MonoidalCategory

/- Keep the signed total comparison as an abstract functor isomorphism. Its
component equation is the API used by representative descent. -/
section
attribute [local irreducible] SheafOfModules.monoidalCategory

end

end SheafOfModules.OpenTensorNormalization
