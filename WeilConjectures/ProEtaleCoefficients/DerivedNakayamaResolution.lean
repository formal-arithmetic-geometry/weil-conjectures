/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions

import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Topology.Algebra.Order.Field
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# The two-term resolution of the finite coefficient sheaves

Source: blueprint main-20261015, sec-proetale-coefficients,
`sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-resolution.md`
(blueprint: det-pe-derived-nakayama-resolution).

All coefficients are continuous condensed rings pulled back from the point. A natural
cone is expressed using the standard cone functor on complexes, with its standard maps.
The comparison with a functor on the derived category also asserts its descent and naturality.

## Main definitions

* `quotientModule`: the continuous finite quotient with its restricted integer action.
* `reductionFunctor`: derived tensor with the pulled-back quotient in degree zero.
* `coneFunctor`: the standard localized mapping-cone model and its maps.

## Main statements

* `derived_nakayama_resolution`: exactness, the natural cone comparison, and the
  specified quotient-power triangles.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open CategoryTheory.Triangulated CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.DerivedNakayama

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section ScalarTools
universe v w
open Category BraidedCategory
namespace UnitScalar
variable (A : Type u) [Category.{v} A] [Preadditive A]
  [MonoidalCategory A] [MonoidalPreadditive A]
private def Scalars := End (𝟙_ A)
private instance : CommRing (Scalars A) := scalarRing A
variable [BraidedCategory A]
omit [Preadditive A] [MonoidalPreadditive A] [BraidedCategory A] in
omit [Preadditive A] [MonoidalPreadditive A] in
omit [Preadditive A] [MonoidalPreadditive A] in
end UnitScalar

namespace UnitScalar
variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{v} A] [MonoidalCategory A] [MonoidalClosed A]
  [MonoidalPreadditive A] [BraidedCategory A] [Abelian.HasFunctorialFlatResolution A]
local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A
end UnitScalar

end ScalarTools

section Sectionwise
universe v w
variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{u + 1}]
end Sectionwise

section QuotientTools
universe v
open Category
namespace PowerQuotients
variable {C : Type u} [Category.{v} C] [Abelian C]
  {U : C} (d : End U) (B : ℕ → C) (r : ∀ n, U ⟶ B n)
  (hz : ∀ n, (d ^ n) ≫ r n = 0)
  (hs : ∀ n, (ShortComplex.mk _ _ (hz n)).ShortExact)
include hz hs in
end PowerQuotients

end QuotientTools

private theorem coefficientTopology :
    (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace =
      @UniformSpace.toTopologicalSpace E
        (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toUniformSpace := by
  have h : (spectralNorm.normedField (Padic l) E).toPseudoMetricSpace =
      (Padic.coefficientExtensionAbsoluteValue l E).toNormedField.toPseudoMetricSpace :=
    PseudoMetricSpace.ext (by
      ext x y
      change spectralNorm (Padic l) E (x - y) = spectralNorm (Padic l) E (-x + y)
      rw [neg_add_eq_sub, ← neg_sub x y,
        spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)])
  exact congrArg (fun m ↦ m.toUniformSpace.toTopologicalSpace) h

private theorem quotientDiscrete (n : ℕ) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    DiscreteTopology (Padic.coefficientExtensionRing l E n) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  cases n with
  | zero =>
    have : Subsingleton (Padic.coefficientExtensionRing l E 0) := by
      apply Ideal.Quotient.subsingleton_iff.mpr
      simp [Padic.coefficientExtensionIdeal]
    exact Subsingleton.discreteTopology
  | succ n =>
    have htop := coefficientTopology l E
    have hb : ∀ x : Padic.coefficientExtensionIntegers l E,
        (nhds x).HasBasis (fun _ : ℕ ↦ True) (fun n ↦
          {y | Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) y =
            Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x}) := by
      have h := Padic.coefficientExtension_integers_coset_basis l E
      change ∀ x, Filter.HasBasis
        (@nhds _ (TopologicalSpace.induced Subtype.val
          (spectralNorm.normedField (Padic l) E).toUniformSpace.toTopologicalSpace) x) _ _ at h
      rw [htop] at h
      exact h
    have hq : IsLocallyConstant
        (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) := by
      apply (IsLocallyConstant.iff_eventually_eq _).mpr
      intro x
      exact (hb x).mem_of_mem (i := n) trivial
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← isQuotientMap_quot_mk.isOpen_preimage]
    exact hq.isOpen_fiber _

end AlgebraicGeometry.ProEtale.DerivedNakayama
