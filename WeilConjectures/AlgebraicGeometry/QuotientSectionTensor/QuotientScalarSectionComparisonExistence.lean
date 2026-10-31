/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarSectionOrdinaryComparisonExistence
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarSectionDerivedComparisonExistence

/-! Comparison and normalization for a fixed sectionwise scalar model. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- For any fixed actual cochain model, normalized ordinary and derived section
comparisons exist.
Source: Stacks 03EK, 06YY, 07A6; this is the comparison part of the
section scalar construction.
(blueprint: lem-sfb-quotient-scalar-section-comparison-existence).

Proof: compare the fixed model with the universal sectionwise scalar model. The
ordinary maps are uniquely determined by the object and map formulas of
change-of-rings and are normalized on the sheafified generators `1 tensor m`.
The derived comparison is the unique counit-compatible isomorphism between the
fixed model and the total left-derived functor. Its universal counit square,
transported through the ordinary comparison and the localization comparison,
gives the displayed equation for every cochain complex. The argument is
independent of flatness and applies to zero rings, empty schemes and unbounded
complexes. -/
theorem scalar_section_comparisons_exists (T : Scheme.{u})
    (model : SectionModel a T) :
    ∃ ordinary : QuotientChange.extension a T ⋙
        (equivalence Λ' T).functor ≅
      (equivalence Λ T).functor ⋙ model.E,
      ∃ derived : D a T ⋙ derivedFunctor Λ' T ≅
        derivedFunctor Λ T ⋙ model.T,
        ScalarSectionNormalized a T
          { model := model, ordinary := ordinary, derived := derived } := by
  obtain ⟨ordinary, hordinary⟩ := scalar_section_ordinary_comparison_exists a T model
  obtain ⟨derived, hderived⟩ :=
    scalar_section_derived_comparison_exists a T model ordinary
  exact ⟨ordinary, derived, hordinary, hderived⟩

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
