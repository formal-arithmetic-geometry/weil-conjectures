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
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses

/-! Stage-3 decomposition helpers for the ringed support-localization triangle.
These declarations isolate independent derived transport obligations. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open WeilConjectures
namespace AlgebraicGeometry.Scheme
/-- Bounded-below preservation for the intrinsic closed upper-shriek derived
functor.  The proof must transport a bounded-below K-injective model through the
left-exact supported-kernel functor and the right-derived comparison.  Source: proof
paragraph 1 of `lem-pur-support-localization-triangle-core-rest`. -/
theorem purSupportLocalizationTriangleBoundedBelowCore
    (P : PurityFiniteSetting.{u}) {Z X U : Scheme.{u}}
    [Z.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    (s : Z ⟶ X) [IsClosedImmersion s] [s.IsOver (Spec (.of P.field.k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hcomp : Set.range s.base = (Set.range j.base)ᶜ)
    : ∀ K : DerivedCategory.Plus
          (proEtaleRingModules X (proEtaleConstantRing X P.Ring)),
        DerivedCategory.TStructure.t.plus
          ((sfIntrinsicClosedUpperShriek s j P.Ring).rightDerivedFunctor.obj K.obj) := by
  letI : IsGrothendieckAbelian.{u + 1}
      (proEtaleRingModules X (proEtaleConstantRing X P.Ring)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, 0}
    (ProEt.topology X) (proEtaleConstantRing X P.Ring)).1
  letI := proEtaleRingModules_hasKInjectiveResolutions X (proEtaleConstantRing X P.Ring)
  letI : EnoughInjectives (proEtaleRingModules X (proEtaleConstantRing X P.Ring)) :=
    IsGrothendieckAbelian.enoughInjectives
  intro K
  obtain ⟨n, hn⟩ := K.property
  letI : K.obj.IsGE n := hn
  exact ⟨n, Functor.isGE_rightDerivedFunctor_obj
    (sfIntrinsicClosedUpperShriek s j P.Ring) K.obj n⟩

end AlgebraicGeometry.Scheme
