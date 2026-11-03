/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData

/-! Existence of the actual sectionwise cochain scalar model. -/

@[expose] public noncomputable section
set_option autoImplicit false

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

/-- The actual sectionwise cochain scalar model exists.
Source: Stacks 06YY; the model is supplied by the project’s universal derived
change-of-rings construction for the section ring map.
(blueprint: lem-sfb-quotient-scalar-section-model-existence).

Proof: apply the existing construction of a `DerivedChangeOfRingsCochainModel`
to the section ring map `sectionQuotient a T`. Its ordinary functor is the
specified sheafified change-of-rings functor, and the construction supplies the
pointwise derived functor, universal counit, triangulated structure, and
K-flat computation fields. No scalar comparison or normalization is used here.
The statement remains valid for zero rings, empty schemes, and arbitrary
unbounded complexes because the construction is unconditional. -/
theorem scalar_section_model_exists (T : Scheme.{u}) :
    Nonempty (SectionModel a T) := by
  exact SheafOfModules.nonempty_derivedChangeOfRingsCochainModel (sectionQuotient a T)

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
