/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData

import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationIsomorphismNormalization
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorRealizationDescent
import WeilConjectures.SixFunctors.AdicQbarRealization.AmbientHomEvaluation.AdicAmbientHomEvaluationComparison
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportRealization

/-! # Evaluation-compatible realization of common-stage adic coefficients

Source: BS Definition 6.8.8, Proposition 6.8.14 and Remark 6.8.15;
HRS Proposition 5.2, Theorem 7.7 and Lemma 7.9
(blueprint: lem-sf-adic-qbar-constructible-realization).

The definitions `GeometricSpace`, `SpaceData`, `Family` are in
`WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData` (blueprint: def-sf-adic-realization-isomorphism-data),
re-exported here.

## Main statements

- `adic_qbar_constructible_realization`: existence with the paper's hypotheses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization

/-- Identity compactification retains the native source and its section presentation.
Source: BS Proposition 6.8.14, via the existing compact-support realization. -/
private theorem native_realization_and_presentation
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (T : GeometricSpace D) :
    ∃ R : LocallyFiniteAdicRealization.Realization l T.base.left,
      (sectionFunctor l T.base.left R).IsEquivalence := by
  let : T.base.left.Over (Spec (CommRingCat.of D.k)) := ⟨T.base.hom⟩
  let : LocallyOfFiniteType (T.base.left ↘ Spec (CommRingCat.of D.k)) := T.finiteType
  let : QuasiCompact (T.base.left ↘ Spec (CommRingCat.of D.k)) := T.quasiCompact
  obtain ⟨P⟩ := ConstructibleExceptionalCoefficients.exists_coefficient_construction
    l (ULift.{u} (PadicAlgCl l)) D hl (𝟙 T.base.left)
  obtain ⟨G, ⟨C⟩⟩ :=
    LocallyFiniteAdicCompactSupport.locally_finite_adic_compact_support_realization
      l D hl P (Compactification.ofIsProper (𝟙 T.base.left))
  refine ⟨C.source, ?_⟩
  exact G.equivalence T.base.left

/-- The inverse transpose is evaluation after tensoring with the transpose.
This is parameter naturality applied to the identity of the Hom object. -/
private theorem source_evaluation_transpose
    {C : Type*} [Category C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)} {H : J.FullSubcategory ⥤ C}
    (S : PodPartialClosed T J H) (L : C) (P : J.FullSubcategory)
    (f : T.obj (L, P.obj.1.unop) ⟶ P.obj.2) :
    T.map (Prod.mkHom (S.transpose L P f) (𝟙 _)) ≫ S.evaluation P = f := by
  apply (S.transpose L P).injective
  simpa only [PodPartialClosed.evaluation, AddEquiv.apply_symm_apply, Category.comp_id]
    using S.parameter_naturality (H.obj P) L P (S.transpose L P f) (S.evaluation P)

/-- Assemble completed tensor normalization and the actual ambient Hom comparison.
Source: BS Remark 6.8.15 and HRS Lemma 7.9, through the recorded descent lemmas. -/
private theorem normalized_tensor_and_hom
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (T : GeometricSpace D)
    (R : LocallyFiniteAdicRealization.Realization l T.base.left)
    (presentation : (sectionFunctor l T.base.left R).IsEquivalence) :
    letI := fun x ↦ sfQbarLocalizationResidueInvertible l D hl
      T.base.left T.base.hom x
    ∃ A : At l T.base.left R,
      (∀ E, Nonempty (FiniteNormalization l T.base.left R A E)) ∧
      HomLaws l T.base.left R A := by
  let := T.separated
  let := T.finiteType
  let := T.quasiCompact
  let := fun x ↦ sfQbarLocalizationResidueInvertible l D hl
    T.base.left T.base.hom x
  obtain ⟨B⟩ := adic_completed_tensor_realization_descent D l hl T.base R
  rcases B with @⟨units, B, N⟩
  have hu : units = (fun x ↦ sfQbarLocalizationResidueInvertible l D hl
      T.base.left T.base.hom x) := Subsingleton.elim _ _
  subst units
  let A : AmbientHomEvaluation.TensorInput l T.base.left R :=
    { closed := B.closed
      models := B.models
      symmetry := B.symmetry
      coherence := B.coherence
      tensor := B.tensor
      unit := B.unit
      associative := B.associative
      left_unit := B.left_unit
      right_unit := B.right_unit
      symmetric := B.symmetric }
  have laws := AmbientHomEvaluation.adic_ambient_hom_evaluation_comparison
    D l hl T.base R presentation A (podCommonClosed l (PadicAlgCl l) T.base.left)
      (podCommonClosed_existsUnique l (PadicAlgCl l) T.base.left).exists.choose_spec
  let A' : At l T.base.left R :=
    { closed := A.closed
      models := A.models
      symmetry := A.symmetry
      coherence := A.coherence
      tensor := A.tensor
      unit := A.unit
      associative := A.associative
      left_unit := A.left_unit
      right_unit := A.right_unit
      symmetric := A.symmetric
      hom_isIso := laws.isIso }
  refine ⟨A', ?_, ?_⟩
  · intro E
    let n := N E
    exact ⟨{ completion := n.completion
             balance := n.balance
             balance_sections := n.balance_sections
             kflat := n.kflat
             ordinary := n.ordinary
             representative := n.representative
             integral_tensor := n.integral_tensor }⟩
  · refine { naturality := laws.naturality, evaluation := laws.evaluation, transpose := ?_ }
    intro L P f
    have h := laws.transpose L P ((podCommonClosed l (PadicAlgCl l) T.base.left).transpose
      L P f)
    rw [source_evaluation_transpose] at h
    exact h

/-- The canonical exact symmetric monoidal common-stage realization in ordinary
modules over the native finite-extension-valued coefficient sheaf, with the
ambient evaluation-transpose Hom comparison and arbitrary-isomorphism coherence.
Source: BS Definition 6.8.8, Proposition 6.8.14 and Remark 6.8.15; HRS Proposition
5.2, Theorem 7.7 and Lemma 7.9
(blueprint: lem-sf-adic-qbar-constructible-realization).

Proof (lem-sf-constructible-exceptional-coefficient-construction,
lem-sf-locally-finite-adic-compact-support-realization): for each geometric space T,
apply the normalized coefficient construction to the identity of T and the native
compact-support realization to its proper identity compactification. Its source
Realization and the section-module equivalence of its NativeGeometry give the native
realization of T and its ordinary section-module presentation; the identity is
separated, of finite type and proper, and T is of finite type over the fixed field.

Apply lem-sf-adic-completed-tensor-realization-descent to this Realization: it gives
the symmetric tensor, unit and coherence data and the finite quotient normalizations,
with the fixed residue-field invertibility instance (by subsingleton equality).

Take the fixed normalized common-stage closed structure podCommonClosed. Its inverse
transpose is evaluation after tensoring with the transpose, by parameter naturality
applied to the identity of the Hom object (lem-pod-derived-automorphism-hom-evaluation).
Apply lem-sf-adic-ambient-hom-evaluation-comparison to the tensor data, the
presentation and this closed structure: it makes the evaluation-transpose Hom
comparison invertible, natural and evaluation-preserving, and its transpose equation
applied to a transpose gives the realized transpose law. This gives At, its finite
normalizations and HomLaws on every T.

Choose these data for all T at once and apply
lem-sf-adic-realization-isomorphism-normalization to them. Its Family carries the
integral, identity, composition, tensor, coefficient-unit and Hom equations for
arbitrary scheme isomorphisms, including semilinear geometric Frobenius, without a
k-linearity hypothesis or a site-perfectness restriction on the permitted Hom pair. -/
theorem adic_qbar_constructible_realization (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) : Nonempty (Family l D) := by
  classical
  have hR := fun T : GeometricSpace D ↦ native_realization_and_presentation D l hl T
  choose R P using hR
  have hA := fun T : GeometricSpace D ↦ normalized_tensor_and_hom D l hl T (R T) (P T)
  choose A N H using hA
  let finite := fun T E ↦ Classical.choice (N T E)
  obtain ⟨F, _⟩ := adic_realization_isomorphism_normalization l D hl R A finite P H
  exact ⟨F⟩

end WeilConjectures.AdicQbarRealization
