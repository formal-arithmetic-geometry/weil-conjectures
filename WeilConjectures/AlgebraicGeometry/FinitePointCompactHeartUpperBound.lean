/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactCohomology
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.FinitePointCompactHeartDenseComparison
import WeilConjectures.AlgebraicGeometry.FinitePointCompactHeartDenseBound

/-! Finite compact-support heart bound split from the finite-point range theorem.
Source: latest blueprint sec-six-functors/sk-lem-finite/sk-lem-finite.proof.md,
Complement (blueprint: lem-sf-finite-point-cohomological-range).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The finite-coefficient compact-support heart estimate.  This is the finite
compact-support clause of `finite_point_cohomological_range`, isolated so that
its dense-refinement, encoding, and compactification comparison argument can be
proved independently.
Source: latest blueprint sec-six-functors/sk-lem-finite/sk-lem-finite.proof.md,
Complement (blueprint: lem-sf-finite-point-compact-heart-upper-bound).

Proof: Replace the chosen compactification by its scheme-theoretically dense refinement and
apply the dense compact-support heart estimate to that refinement. The refinement has the same
source dimension by the dense-bound helper. Use the finite constant-model compactification
comparison to identify the native lower-shriek object for the original compactification with the
one for the refinement, then transport the `IsLE (2 * d)` property across this isomorphism.
-/
theorem finite_point_compact_heart_upper_bound_split
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∀ n : ℕ, 1 ≤ n →
      ∀ (X : Over (Spec (.of D.k)))
        [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
        (c : Compactification X.hom)
        (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
          (condensedRingObj
            (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) X.left)),
        IsConstantModelConstructible
          (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) X.left M →
        ∀ d : ℕ, topologicalKrullDim X.left = (d : WithBot ℕ∞) →
          ((rightDerivedLowerShriekOfCompactification
            (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) c).obj
            ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE (2 * (d : ℤ)) := by
  intro n hn X _ _ _ c M hM d hd
  let c' := c.denseRefinement
  have hc' : IsSchemeTheoreticallyDominant c'.i :=
    c.isSchemeTheoreticallyDominant_denseRefinement_i
  have hbound := finite_point_compact_heart_upper_bound_dense
    D ℓ hℓ E n hn X c' hc' M hM d hd
  obtain ⟨hcomp⟩ := finite_point_compact_heart_dense_comparison
    D ℓ hℓ E n hn X c M hM
  exact ⟨(DerivedCategory.TStructure.t.le (2 * (d : ℤ))).prop_of_iso hcomp.symm hbound.le⟩

end AlgebraicGeometry.ProEtale.CondensedRing
