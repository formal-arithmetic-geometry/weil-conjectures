/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystem
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Submission.WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import Submission.WeilConjectures.AlgebraicGeometry.CartierComplementFrame
import Submission.WeilConjectures.AlgebraicGeometry.CartierReductionData
import Submission.WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import Submission.WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
import Submission.WeilConjectures.AlgebraicGeometry.OpenClosedIntegralSections
import Submission.WeilConjectures.AlgebraicGeometry.PicardTensorDualComparisonIso
import Submission.WeilConjectures.AlgebraicGeometry.PullbackMonoidalUnitComparison
import Submission.WeilConjectures.AlgebraicGeometry.PullbackTensorComposition
import Submission.WeilConjectures.AlgebraicGeometry.ScalarUnitExt
import Submission.WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
import Submission.WeilConjectures.AlgebraicGeometry.SupportedCartierBoundaryExistence
import Submission.WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
import Submission.WeilConjectures.AlgebraicGeometry.SupportedKummerChernRealization
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import Submission.WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import Submission.WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison
import Submission.WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import Submission.WeilConjectures.CategoryTheory.FlatScalarUnit
import Submission.WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction
import Submission.WeilConjectures.CategoryTheory.PushoutShortExactSequence
import Submission.WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation
import Submission.WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
import Submission.WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
import Submission.WeilConjectures.CategoryTheory.Sites.RelativeTorsorExtension
import Submission.WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Existence of an ordinary supported Cartier Kummer map

Source: Stacks Project, Tags 03PL and 0A45; blueprint
sec-smooth-purity/sk-prop-sf-cbc/lem-amb-cartier-kummer-map.md
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section

-- Use the same category-instance proofs as the recorded derived module category.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

end

/-- The unique-boundary clause of ordinary_supported_kummer, with its other witnesses hidden.
Source: Stacks 03PL, 0A45 (auxiliary; not a blueprint node).
Proof: apply supported_cartier_boundary_existsUnique directly. Its unique representative
is the boundary class used in ordinary_supported_kummer. This avoids normalizing the
pullback and scalar witnesses in consumers.
-/
theorem ordinary_supported_kummer_uniqueBoundary (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) :
    ∃! κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2,
      SupportedKummerBoundary A N hA i hI hT κ := by
  exact supported_cartier_boundary_existsUnique T N hN A hA hT i hI

end AlgebraicGeometry.Etale
