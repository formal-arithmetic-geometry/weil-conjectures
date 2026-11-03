/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicFibreComparison.AdicStratifiedPullbackInterface
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTStructure

/-! # Normalized fibre comparison data

Source: Bhatt--Scholze 6.8.4, 6.8.14 and 6.8.15
(blueprint: def-per-adic-fibre-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genCtorIdx false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.AdicFibreComparison
open ContinuousRational

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]
  (R : ContinuousRational.Family.{u} l)

/-- The normalized finite-stage fibres are the dependency's intrinsic, lattice-normalized
fibres, simultaneously at every scheme and coefficient field.
Source: BS 6.8.4 (blueprint: def-per-adic-fibre-comparison-data). -/
abbrev Fibres := ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : FiniteTypeBase k),
  NormalizedFibre.Assertions l E (base l X) (R.realization E (base l X))

variable (E L : Type u) [Field E] [Field L] [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]

variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The already specified heart inclusion with its shift parameters fixed explicitly.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-comparison-data). -/
def finiteHeartInclusion (X : FiniteTypeBase k) :
    NormalizedFibre.Heart l E (base l X) ⥤
      PbcRationalCategory X.scheme (pbcIntegralDatum l E) (pbcUniformizer l E) :=
  (localizedT l E (base l X)).heart.ι

/-- A finite-stage heart object lies in the common-stage heart after the actual inclusion.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-comparison-data).
Proof: the common standard heart is the isomorphism closure of the finite-stage hearts,
by the recorded common-stage truncation theorem; apply it to the inclusion itself. -/
theorem stageHeartMem (X : FiniteTypeBase k) (A : Padic.FiniteCoefficientFields l Ω)
    (F : NormalizedFibre.Heart l (pbcFiniteField.{u} l Ω A) (base l X)) :
    (pbcQbarStandardT l Ω X.scheme).heart
      (((pbcScalarSystem l Ω X.scheme (base l X).dimension
        (base l X).prime_unit).ι A).obj F.obj) := by
  have hF := F.property
  have hImage := (pbc_localized_tstructure X.scheme l
    (pbcFiniteField.{u} l Ω A)).choose_spec.1 F.obj
  have hCommon := (pbcQbarStandardT_existsUnique l Ω X.scheme).exists.choose_spec.1 0
  change (pbcQbarStandardT_existsUnique l Ω X.scheme).exists.choose.heart _
  constructor
  · rw [hCommon.1]
    obtain ⟨M, hM, ⟨e⟩⟩ := (hImage.1).mp hF.1
    exact ⟨A, M, hM, ⟨((pbcScalarSystem l Ω X.scheme
      (base l X).dimension (base l X).prime_unit).ι A).mapIso e⟩⟩
  · rw [hCommon.2]
    obtain ⟨M, hM, ⟨e⟩⟩ := (hImage.2).mp hF.2
    exact ⟨A, M, hM, ⟨((pbcScalarSystem l Ω X.scheme
      (base l X).dimension (base l X).prime_unit).ι A).mapIso e⟩⟩

/-- Literal inclusion of the finite-stage heart into the common-stage heart.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-comparison-data). -/
def stageHeart (X : FiniteTypeBase k) (A : Padic.FiniteCoefficientFields l Ω) :=
  ObjectProperty.lift (pbcQbarStandardT l Ω X.scheme).heart
    (finiteHeartInclusion l (pbcFiniteField.{u} l Ω A) X ⋙
      (pbcScalarSystem l Ω X.scheme (base l X).dimension (base l X).prime_unit).ι A)
    (stageHeartMem l Ω X A)

/-- The canonical embedding of the existing small finite coefficient model.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-comparison-data). -/
def stageEmbedding (A : Padic.FiniteCoefficientFields l Ω) :
    pbcFiniteField.{u} l Ω A →+* Ω :=
  A.val.subtype.comp (Shrink.algEquiv ℚ_[l] A.val).toRingHom

/-- Exact common-stage fibres, normalized on every finite-stage heart and all its maps.
Source: BS 6.8.14 (blueprint: def-per-adic-fibre-comparison-data). -/
structure CommonPoint (ω : Fibres (k := k) l R) (X : FiniteTypeBase k)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (x : Spec (.of κ) ⟶ X.scheme) where
  functor : (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory ⥤
    ModuleCat.{max (u + 1) v} Ω
  [additive : functor.Additive]
  finite : ∀ F, FiniteDimensional Ω (functor.obj F)
  exact : ∀ S : ShortComplex (pbcQbarStandardT l Ω X.scheme).heart.FullSubcategory,
    S.ShortExact → (S.map functor).ShortExact
  finite_stage : ∀ A : Padic.FiniteCoefficientFields l Ω,
    stageHeart l Ω X A ⋙ functor ≅
      ((ω (pbcFiniteField.{u} l Ω A) X).point κ x).functor ⋙
        ModuleCat.extendScalars (stageEmbedding l Ω A)

attribute [instance] CommonPoint.additive

end AlgebraicGeometry.Scheme.AdicFibreComparison
