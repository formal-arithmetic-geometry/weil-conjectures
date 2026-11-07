/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.InternalSectionTotalComparison
public import Submission.WeilConjectures.AlgebraicGeometry.InternalSectionDerivedTensorComparison

public import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Hom
public import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplexProjections
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Submission.WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import Submission.WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import Submission.WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import Submission.WeilConjectures.CategoryTheory.RingObjects.Ab
public import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Submission.WeilConjectures.CategoryTheory.SheafTensor
public import Submission.WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import Submission.WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Submission.WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3
/-! # Normalized internal-to-sectionwise derived tensor comparison

Source: Stacks Project, Tags 08J9, 08JA and 08JB; blueprint module objects and
derived tensor--Hom (blueprint: def-sfb-internal-section-derived-tensor-comparison).

## Main definitions

* `TensorComparison`: the canonical tensor comparison, normalized on K-flat models.
* `totalComparison`: the fixed comparison of the concrete sum-total complexes.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open scoped CategoryTheory.Obj
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open CategoryTheory.InternalAbelianSheafModule WeilConjectures

namespace AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃


variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})

/-- The fixed comparison on the concrete native total complexes. The preceding
unique characterization determines its data, including every summand map.
Source: Stacks 03EK, 06YL
(blueprint: def-sfb-internal-section-derived-tensor-comparison). -/
def totalComparison (P Q : CochainComplex (Internal Λ X) ℤ) :
    (complexForward Λ X).obj (internalTotalTensor Λ X P Q) ≅
    (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)).obj
      ((complexForward Λ X).obj P, (complexForward Λ X).obj Q) :=
  complexTensorIso Λ X P Q

/-- The fixed global total map is the canonical summand-normalized site map.
Source: Stacks 06YL (blueprint: def-sfb-internal-section-derived-tensor-comparison).
Proof: unfold the two named specializations; both are the same normalized map. -/
theorem totalComparison_heq (P Q : CochainComplex (Internal Λ X) ℤ) :
    HEq (totalComparison Λ X P Q)
      (ordinaryComplexTensorIsoForSite (Scheme.ProEt.topology X)
        (condensedRingObj Λ X) P Q) := by
  unfold totalComparison complexTensorIso
  rfl

/-- Closed structures for the fixed global ringed-site Hom.
Source: Stacks 08J9 (blueprint: def-sfb-internal-section-derived-tensor-comparison). -/
def GlobalClosedStructureType := CoefficientClosedStructure (hom Λ X)

/-- Tensor models for that fixed global closed structure.
Source: Stacks 06YS (blueprint: def-sfb-internal-section-derived-tensor-comparison). -/
def GlobalTensorModelsType (S : GlobalClosedStructureType Λ X) :=
  CoefficientTensorModels.{u, u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (ring Λ X) S

/-- Natural comparisons of the fixed global native tensor.
Source: Stacks 06YS (blueprint: def-sfb-internal-section-derived-tensor-comparison). -/
def GlobalTensorComparisonIsoType (S : GlobalClosedStructureType Λ X) :=
  Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) ⋙ forward Λ X ≅
    ((forward Λ X).prod (forward Λ X)) ⋙ S.tensor

/-- The representative-normalization predicate for a derived tensor comparison.
Separating this predicate keeps structure projections from expanding the concrete
localization and total-complex implementations.
Source: Stacks 06YS, 08J9
(blueprint: def-sfb-internal-section-derived-tensor-comparison). -/
def tensorComparisonNormalized
    (S : GlobalClosedStructureType Λ X)
    (T : GlobalTensorModelsType Λ X S)
    (iso : GlobalTensorComparisonIsoType Λ X S) : Prop :=
  tensorLocalizationSquareHEq DerivedCategory.Q DerivedCategory.Q
    (complexForward Λ X) (forward Λ X) (localizationIso Λ X)
    (Functor.uncurry.obj (CondensedRing.derivedTensor Λ X))
    (MonoidalCategory.tensor (CochainComplex (Internal Λ X) ℤ)) S.tensor
    (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X))
    (localizationTensorMap Λ X) (totalComparison Λ X)
    (CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology X) (R := ring Λ X))
    (CoefficientTensorModels.iso.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring Λ X) S T) iso

/-- Tensor comparison with the fixed K-flat localization normalization.
The complex comparison is the dependency's canonical comparison, not extra data.
K-flatness is tested on the images under the exact equivalence; preservation and
reflection in lem-pe-internal-section-tensor-comparison identify this with the
internal K-flat test, so it restricts only representatives and not derived inputs.
Source: Stacks 06YS, 08J9 (blueprint: def-sfb-internal-section-derived-tensor-comparison). -/
structure NormalizedGlobalTensorComparisonData {I : Type u₀} (condition : I → Prop) where
  iso : I
  normalization : condition iso

/-- The fixed global comparison record, with abstract endpoints.
Source: Stacks 06YS (blueprint: def-sfb-internal-section-derived-tensor-comparison). -/
abbrev TensorComparison
    (S : GlobalClosedStructureType Λ X)
    (T : GlobalTensorModelsType Λ X S) :=
  NormalizedGlobalTensorComparisonData (I := GlobalTensorComparisonIsoType Λ X S)
    (tensorComparisonNormalized Λ X S T)

end AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
