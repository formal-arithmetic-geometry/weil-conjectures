/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.ConstructibleSheaf.Refinement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Exact closure of constructible sheaves in the site coefficient universe
Source: Stacks Tags 09B5 and 093U, with finite global partitions.
(blueprint: lem-weil-constructible-coefficient-serre). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

namespace CoefficientSerre

variable (T : Scheme.{u}) (B : Type (u + 1)) [CommRing B]

end CoefficientSerre

namespace CoefficientSerre
open CategoryTheory.Functor
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type (u + 1)) [CommRing A]

end CoefficientSerre

namespace CoefficientSerre
open ProEtale
variable (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]

private theorem fixed_reflects_constructible
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hG : IsConstructible A ((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj G)) :
    IsConstructibleSheaf G := by
  obtain ⟨H, hH, ⟨e⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A hG
  have := hH
  exact IsConstructibleSheaf.of_iso
    ((comparisonUpperStar (ModuleCat.{u + 1} A) T).preimageIso e)

private theorem fixed_kernel_cokernel
    (F G : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)) (f : F ⟶ G)
    (hF : IsConstructible A F) (hG : IsConstructible A G) :
    IsConstructible A (kernel f) ∧ IsConstructible A (cokernel f) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A hF
  obtain ⟨H, hH, ⟨e'⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A hG
  have := hE
  have := hH
  let L := comparisonUpperStar (ModuleCat.{u + 1} A) T
  obtain ⟨g, hg⟩ := L.map_surjective (e.hom ≫ f ≫ e'.inv)
  have hw : L.map g ≫ e'.hom = e.hom ≫ f := by simp [hg]
  have := IsConstructibleSheaf.kernel g
  have := IsConstructibleSheaf.cokernel g
  exact ⟨isConstructible_of_iso (PreservesKernel.iso L g ≪≫
      kernel.mapIso (L.map g) f e e' hw)
      (isConstructible_comparisonUpperStar_obj (kernel g)),
    isConstructible_of_iso (PreservesCokernel.iso L g ≪≫
      cokernel.mapIso (L.map g) f e e' hw)
      (isConstructible_comparisonUpperStar_obj (cokernel g))⟩

private theorem fixed_extension
    (S : ShortComplex (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} A)))
    (hS : S.ShortExact) (h₁ : IsConstructible A S.X₁)
    (h₃ : IsConstructible A S.X₃) : IsConstructible A S.X₂ := by
  let L := comparisonUpperStar (ModuleCat.{u + 1} A) T
  let R := comparisonLowerStar (ModuleCat.{u + 1} A) T
  let adj := comparisonAdjunction (ModuleCat.{u + 1} A) T
  obtain ⟨E₁, hE₁, ⟨e₁⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A h₁
  obtain ⟨E₃, hE₃, ⟨e₃⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj A h₃
  have h₂ := etaleOrigin_of_shortExact hS ⟨E₁, ⟨e₁⟩⟩ ⟨E₃, ⟨e₃⟩⟩
  have hc₁ : IsIso (adj.counit.app S.X₁) :=
    adj.isIso_counit_app_iff_mem_essImage.mpr ⟨E₁, ⟨e₁⟩⟩
  have hc₂ : IsIso (adj.counit.app S.X₂) :=
    adj.isIso_counit_app_iff_mem_essImage.mpr h₂
  have hc₃ : IsIso (adj.counit.app S.X₃) :=
    adj.isIso_counit_app_iff_mem_essImage.mpr ⟨E₃, ⟨e₃⟩⟩
  let e : (S.map R).map L ≅ S := ShortComplex.isoMk
    (asIso (adj.counit.app S.X₁)) (asIso (adj.counit.app S.X₂))
    (asIso (adj.counit.app S.X₃)) (adj.counit.naturality S.f).symm
    (adj.counit.naturality S.g).symm
  have he : ((S.map R).map L).ShortExact := (ShortComplex.shortExact_iff_of_iso e).mpr hS
  have hR := ShortExact.reflects_shortExact_of_faithful L he
  have hR₁ : IsConstructibleSheaf
      (FA := fun M N : ModuleCat.{u + 1} A ↦ M →ₗ[A] N)
      (CA := fun M : ModuleCat.{u + 1} A ↦ M) (R.obj S.X₁) := fixed_reflects_constructible T A _
    (isConstructible_of_iso (asIso (adj.counit.app S.X₁)).symm h₁)
  have hR₃ : IsConstructibleSheaf
      (FA := fun M N : ModuleCat.{u + 1} A ↦ M →ₗ[A] N)
      (CA := fun M : ModuleCat.{u + 1} A ↦ M) (R.obj S.X₃) := fixed_reflects_constructible T A _
    (isConstructible_of_iso (asIso (adj.counit.app S.X₃)).symm h₃)
  have hR₁' : IsConstructibleSheaf (S.map R).X₁ := hR₁
  have hR₃' : IsConstructibleSheaf (S.map R).X₃ := hR₃
  have hR₂ : IsConstructibleSheaf (R.obj S.X₂) := IsConstructibleSheaf.of_shortExact hR
  exact isConstructible_of_iso (asIso (adj.counit.app S.X₂))
    (isConstructible_comparisonUpperStar_obj (R.obj S.X₂))

end CoefficientSerre

end AlgebraicGeometry.Scheme
