/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystem
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.AlgebraicGeometry.CartierComplementFrame
import WeilConjectures.AlgebraicGeometry.CartierReductionData
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import WeilConjectures.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
import WeilConjectures.AlgebraicGeometry.OpenClosedIntegralSections
import WeilConjectures.AlgebraicGeometry.PicardTensorDualComparisonIso
import WeilConjectures.AlgebraicGeometry.PullbackMonoidalUnitComparison
import WeilConjectures.AlgebraicGeometry.PullbackTensorComposition
import WeilConjectures.AlgebraicGeometry.ScalarUnitExt
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
import WeilConjectures.AlgebraicGeometry.SupportedCartierBoundaryExistence
import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
import WeilConjectures.AlgebraicGeometry.SupportedKummerChernRealization
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import WeilConjectures.CategoryTheory.FlatScalarUnit
import WeilConjectures.CategoryTheory.InjectiveSheafMonoRestriction
import WeilConjectures.CategoryTheory.PushoutShortExactSequence
import WeilConjectures.CategoryTheory.Sites.ContractedProductPresentation
import WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
import WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
import WeilConjectures.CategoryTheory.Sites.RelativeTorsorExtension
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

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
