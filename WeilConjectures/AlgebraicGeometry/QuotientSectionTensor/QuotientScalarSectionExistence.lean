/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarSectionModelExistence
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarSectionComparisonExistence

/-! # A step of the normalized quotient section comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

open ModuleRingedComparison

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- The actual section change-of-rings model admits the normalized internal comparison.
Source: Stacks 03EK, 03EL, 06YY; parent proof step 1.
(blueprint: lem-sfb-quotient-scalar-section-existence).

Proof: take the sheafified sectionwise scalar-extension functor and its everywhere
defined total left derived functor with its universal cochain counit. The ordinary
internal/section scalar adjunction gives the comparison on module sheaves: inserting
the scalar unit internally maps to the sheafified generator 1 tensor m. Transport
this comparison termwise to complexes and through the exact section equivalences.
Both composites are total left derived functors of the same ordinary composite;
the counit-compatible unique isomorphism gives the derived comparison. Its defining
universal-counit square, with the two complex-composition comparisons inserted,
is exactly the second normalization equation, for every complex. This construction
uses no exactness of scalar extension and works for zero modules, zero target rings,
empty schemes, and arbitrary unbounded complexes. -/
theorem scalar_section_exists (T : Scheme.{u}) :
    ∃ c : ScalarSectionData a T, ScalarSectionNormalized a T c := by
  obtain ⟨model⟩ := scalar_section_model_exists a T
  obtain ⟨ordinary, derived, hnormalized⟩ :=
    scalar_section_comparisons_exists a T model
  exact ⟨{ model := model, ordinary := ordinary, derived := derived }, hnormalized⟩

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
