/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteProCoefficientCounitTransport
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionCompatibilities
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import all WeilConjectures.AlgebraicGeometry.DerivedCategories
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import all WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import all WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import all WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
import all WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.RingTheory.Noetherian.Defs
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import all WeilConjectures.CategoryTheory.Ringed.RingedProEtaleTorAmplitudeOfUniverses
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Limits.Final
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

/-! # Two-level finite smooth reduction

Source: main-20261015, sk-prop-sp-orientation and sk-lem-sp-reduction/compatibilities
(blueprint: lem-pur-finite-smooth-two-level-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

private theorem reductionOriginIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) [IsNoetherian T]
    (K : proCategory A T) (hK : IsCtf A T K) : IsIso (originReductionMap φ T K) := by
  have := intrinsicOriginCounit A T K hK
  have hp := ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ T
    ((origin A T).obj K) (actualOriginCtf A T K hK).2
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat B) T
    ((ordinaryScalar φ T).obj ((origin A T).obj K)) hp
  unfold originReductionMap
  rw [Adjunction.homEquiv_unit]
  infer_instance

private theorem reductionOriginInverseIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : proCategory A T) (hK : IsCtf A T K) : IsIso (originInverse A T K) := by
  have hc := intrinsicOriginCounit A T K hK
  unfold originInverse
  rw [dif_pos hc]
  infer_instance

private theorem reductionPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) (K : proCategory A Y) (hK : IsCtf A Y K) :
    IsIso (proPullbackMap φ f K) := by
  have := reductionOriginInverseIso A Y K hK
  have := scalarOriginCounit φ Y K hK
  have := reductionOriginIso φ Y K hK
  unfold proPullbackMap pullbackToOrigin pullbackFromOrigin
  infer_instance

end AlgebraicGeometry.Etale.FiniteSmoothPurity
