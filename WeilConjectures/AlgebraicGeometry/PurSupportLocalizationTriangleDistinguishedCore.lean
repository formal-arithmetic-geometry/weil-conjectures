/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurSupportTriangle
public import WeilConjectures.AlgebraicGeometry.PurTriangleMeaning
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ConstructibleExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.ClosedFiniteTransport.ClosedFiniteAdjointCounitTransport
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedClosedKernelAdjoint
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedAmbient
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.ExactDerivedAdjunctionUnitShift
public import WeilConjectures.CategoryTheory.Triangulated.Recollement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenClosedTriangle
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRestrictionInjectives
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.ClosedLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence

/-! Stage-3 decomposition helpers for the ringed support-localization triangle.
These declarations isolate independent derived transport obligations. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open WeilConjectures
namespace AlgebraicGeometry.Scheme
/-- Distinguishedness and resolution comparison for the specified support triangle.
This isolates the cone contraction, quotient transport, and comparison with an arbitrary
derived adjunction.  Source: proof paragraphs 2--3 of
`lem-pur-support-localization-triangle-core-rest`. -/
theorem purSupportLocalizationTriangleDistinguishedCore
    (A : Type u) [CommRing A] [Finite A] {Z X U : Scheme.{u}}
    [IsNoetherian X]
    (s : Z ⟶ X) [IsClosedImmersion s]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range s.base = (Set.range j.base)ᶜ)
    (hS : PreservesFiniteColimits (sfConstantModuleDirectImage s A))
    (a0 : sfConstantModuleDirectImage s A ⊣ sfIntrinsicClosedUpperShriek s j A)
    (adj : (sfConstantModuleDirectImage s A).rightDerivedFunctor ⊣
      (sfIntrinsicClosedUpperShriek s j A).rightDerivedFunctor) :
    ∀ (K : CochainComplex.Plus
          (proEtaleRingModules X (proEtaleConstantRing X A)))
      (r : CochainComplex.KInjectiveResolutionChoice K.obj)
      (hI : ∀ n : ℤ, Injective (r.complex.X n)),
      supportTriangle s j hcomp A K r hI ∈
          distTriang (proEtaleDerivedCategory X A) ∧
        ∃ δ, ∃ e : supportTriangle s j hcomp A K r hI ≅
          purSupportAdjunctionTriangle s j A adj (DerivedCategory.Q.obj K.obj) δ,
          DerivedCategory.Q.map r.map ≫ e.hom.hom₂ = 𝟙 _ := by
  sorry

end AlgebraicGeometry.Scheme
