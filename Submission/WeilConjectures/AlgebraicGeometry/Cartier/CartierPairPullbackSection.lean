/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import Submission.WeilConjectures.AlgebraicGeometry.RawModuleScalarComparison.RawModuleScalarDerivedPullbackIso
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Kummer
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import Submission.WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.EtalePicard
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Submission.WeilConjectures.SixFunctors.BaseChange.Square
public import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.TensorPullback
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerBoundary
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import Submission.WeilConjectures.AlgebraicGeometry.Modules.Dual
import Submission.WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
import Submission.WeilConjectures.AlgebraicGeometry.Modules.HomTensor.LocallyFree
import Submission.WeilConjectures.AlgebraicGeometry.DualTensorHomComparison
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import Submission.WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Submission.WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import Submission.WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Submission.WeilConjectures.AlgebraicGeometry.Modules.AffineDescent
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import Submission.WeilConjectures.AlgebraicGeometry.Relative.RelativeEtaleCohomology
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.CategoryTheory.Preadditive.Comma
import Submission.WeilConjectures.CategoryTheory.Sites.FramedLift.FramedLifts
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Submission.WeilConjectures.AlgebraicGeometry.CartierPoleBoundary
import Submission.WeilConjectures.CategoryTheory.Sites.WithSection.TorsorWithSection
import Submission.WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation
import Submission.WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Submission.WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import Submission.WeilConjectures.CategoryTheory.Sites.RelativeTorsorExtension
import Submission.WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Submission.WeilConjectures.CategoryTheory.Sites.Torsor
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Abelian.Exact
import Submission.WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
import Submission.WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Submission.WeilConjectures.CategoryTheory.YonedaExtension.YonedaExtensionData
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Submission.WeilConjectures.AlgebraicGeometry.Modules.IdealSheafFiniteType
import Submission.WeilConjectures.AlgebraicGeometry.EffectiveCartierSum
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import Submission.WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison
import Submission.WeilConjectures.AlgebraicGeometry.RelativeCone.PurityRelativeCone
import Submission.WeilConjectures.AlgebraicGeometry.OpenClosedIntegralSections
import Submission.WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
import Submission.WeilConjectures.SixFunctors.OpenClosed.Exact
import Submission.WeilConjectures.EtaleCohomology.Purity.Smooth.KummerCoefficients
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Submission.WeilConjectures.SixFunctors.Finite.BaseChange
import Submission.WeilConjectures.AlgebraicGeometry.CartierComplementFrame
import Submission.WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance
import Submission.WeilConjectures.AlgebraicGeometry.InternalHomRestrictScheme
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Pullback of the Cartier line bundle with its canonical section

Source: Stacks Project, Tag 0C4U, and the relative Cartier class in the blueprint
proof of lem-amb-cartier-kummer-map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Etale

private theorem comparison_right_unit {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [MonoidalCategory C] [MonoidalCategory D]
    (H F : C ⥤ D) [F.Monoidal] (e : H ≅ F) (J : C) :
    (e.hom.app J ⊗ₘ e.hom.app (𝟙_ C)) ≫
        (Functor.Monoidal.μIso F J (𝟙_ C)).hom ≫ e.inv.app (J ⊗ (𝟙_ C)) ≫
        H.map (ρ_ J).hom =
      (𝟙 _ ⊗ₘ (e.hom.app (𝟙_ C) ≫ Functor.OplaxMonoidal.η F)) ≫
        (ρ_ (H.obj J)).hom := by
  apply (cancel_mono (e.hom.app J)).mp
  simp only [Category.assoc]
  rw [e.hom.naturality (ρ_ J).hom]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.OplaxMonoidal.right_unitality_hom F J]
  simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.μ_δ_assoc]
  rw [← rightUnitor_naturality, ← id_tensorHom, ← tensorHom_id,
    tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.comp_id, Category.id_comp]

end AlgebraicGeometry.Etale
