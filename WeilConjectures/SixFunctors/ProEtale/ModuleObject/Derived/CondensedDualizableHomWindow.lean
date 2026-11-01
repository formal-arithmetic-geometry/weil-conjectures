/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided

/-! # The Hom window of a dualizable condensed complex

The argument takes place in the ordinary derived category of internal modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A dualizable first input gives the canonical dual-tensor comparison and the
sharp Hom Tor interval. Source: the perfect-complex paragraph of the current
prop-functor-package proof; the tensor and exact-pairing Tor theorems
(blueprint: lem-e6-condensed-dualizable-hom-window).

Proof: use the given dual to make the canonical evaluation comparison invertible.
Its value at the tensor unit supplies the canonical exact pairing with the Hom
dual. Symmetry supplies the reverse pairing. The exact-pairing Tor theorem puts
this dual in [-b,-a]; tensoring with the second input adds [c,d]. Transport that
interval through the canonical evaluation isomorphism. -/
theorem condensedDualizableHomWindow
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (K L : moduleDerived Λ X) (hK : IsDualizable K) :
    IsIso (MonoidalClosed.ihomUnitTensorToIhom K L) ∧
      ∀ a b c d : ℤ, a ≤ b → c ≤ d →
        DerivedCategory.torAmplitudeIn _ a b K →
        DerivedCategory.torAmplitudeIn _ c d L →
        DerivedCategory.torAmplitudeIn _ (c - b) (d - a)
          (internalHomObj Λ X K L) := by
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  obtain ⟨_⟩ := hK
  let := BraidedCategory.exactPairing_swap K Kᘁ
  have h (M : moduleDerived Λ X) :
      IsIso (MonoidalClosed.ihomUnitTensorToIhom K M) :=
    MonoidalClosed.isIso_ihomUnitTensorToIhom Kᘁ K M
  refine ⟨h L, ?_⟩
  intro a b c d _ _ hKt hLt
  let := h K
  let := MonoidalClosed.exactPairingOfIsIso K
  let := BraidedCategory.exactPairing_swap ((ihom K).obj (𝟙_ (moduleDerived Λ X))) K
  have hd := DerivedCategory.torAmplitudeIn_of_exactPairing
    (L := (ihom K).obj (𝟙_ (moduleDerived Λ X))) hKt
  have ht := DerivedCategory.torAmplitudeIn_tensor hd hLt
  let := h L
  apply (DerivedCategory.torAmplitudeIn _ (c - b) (d - a)).prop_of_iso
    (asIso (MonoidalClosed.ihomUnitTensorToIhom K L))
  convert ht using 1 <;> omega

end AlgebraicGeometry.ProEtale.CondensedRing
