/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusCohomologyRealization

/-! # Canonical factors of the cohomology coefficient comparison

Source: Deligne, Weil II (1.1.1)(d), (1.1.14), coefficient extension and cohomology
(blueprint: def-weil-frobenius-cohomology-comparison-factors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w x y z u'

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
namespace CohomologyRealization
open AlgebraicallyClosedCoefficients (Index)
open GeneralAlgebraicallyClosedCoefficients (stageSystem)

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard

set_option allowUnsafeReducibility true in
attribute [local irreducible] frobeniusCohomologyCoefficientExtension
  frobeniusCohomologyRationalFunctor frobeniusCohomologyRationalScalar
  operationStageTransitionIso frobeniusCoefficientTower DerivedCategory.fieldScalarTower

open AlgebraicallyClosedCoefficients (Coefficient coefficientInclusion coefficientInclusion_laws)

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The actual scalar-and-size functor into D(Ω).
Source: Deligne, Weil II (1.1.1)(d), coefficient extension
(blueprint: def-weil-frobenius-cohomology-comparison-factors). -/
abbrev coefficient (E : Index l Ω) :=
  frobeniusCohomologyCoefficientExtension (frobeniusCohomologyStageEmbedding.{u, v} l Ω E)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom] (c₀ : Compactification Y₀.hom) (compact : Bool)

section ComparisonRecords

variable {I : Type u'} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {B : I → Type w} [bCategory : ∀ i, Category.{x} (B i)]
  {D : Type y} [Category.{z} D] {S : StageSystem C}


end ComparisonRecords

end CohomologyRealization
end WeilConjectures
