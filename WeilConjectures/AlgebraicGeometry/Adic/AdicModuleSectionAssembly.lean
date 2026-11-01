/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleTensorHomComparison

/-! # Closed comparison for the explicit adic section equivalence -/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

/-- The normalized comparison at one base, with the actual coefficient ring sheaf.
Source: Stacks Project, Modules on Sites, Tags 03CV and 03EO, and the native adic
module presentation (blueprint: lem-sf-adic-module-section-comparison).

Proof: evaluate a native action after the canonical tensor comparison. The action
axioms become the sectionwise module axioms, as in `comparisonSectionModule`. Conversely
restrict scalars along constant functions to obtain the underlying vector-space
sheaf; extend the sectionwise action through vector-space sheafification. These
assignments are inverse because the tensor comparison detects maps. They leave
sections, restrictions and morphisms unchanged. The regular action is multiplication.
The native balanced coequalizer and the sheafified sectionwise tensor represent the
same balanced pairings, so their universal arrows give mutually inverse natural
comparisons, with the stated pure-tensor formula. Curry a pairing on every slice by
sending a section z to the morphism x ↦ b(z|_W,x); evaluation reverses currying.
This identifies the slice Hom with the native right adjoint, preserving its counit.
Transposing the braided evaluation gives bidual evaluation and its section formula.
Finally the equivalence preserves coproducts; the unit comparison on each summand
gives the free comparison with its coordinate formula, including the empty sum.
The coefficient ring used throughout is `comparisonRing`, so the last equality is
reflexive. -/
theorem adicModuleSectionComparison (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    ∃ P : AdicModuleSectionComparison l X, P.R = comparisonRing l X := by
  obtain ⟨q⟩ := adicModuleTensorHomComparison l X
  refine ⟨{
    R := comparisonRing l X
    coefficient := fun V ↦ RingEquiv.refl _
    coefficient_identity := fun V r ↦ HEq.rfl
    coefficient_naturality := fun f r ↦ rfl
    E := adicSectionModuleEquivalence l X
    sectionsEquiv := fun M V ↦ AddEquiv.refl _
    section_identity := fun M V x ↦ HEq.rfl
    section_restriction := fun M V W f x ↦ rfl
    section_map := fun f V x ↦ rfl
    action := fun M V r x ↦ rfl
    unitIso := comparisonUnitIso l X
    unit_sections := fun V r ↦ rfl
    tensorIso := q.tensorIso
    tensor_naturality := q.tensor_naturality
    tensor_sections := q.tensor_sections
    homIso := q.homIso
    hom_naturality := q.hom_naturality
    evaluation := q.evaluation
    bidual := adicNativeBidual
    bidual_transpose := adicNativeBidual_transpose
    bidual_sections := q.bidual_sections
    freeIso := fun n ↦ comparisonFreeIso l X (ULift.{u + 1} (Fin n))
    free_coordinates := fun n i ↦ comparisonFreeIso_coordinates l X _ i }, rfl⟩

end AlgebraicGeometry.ProEtale
