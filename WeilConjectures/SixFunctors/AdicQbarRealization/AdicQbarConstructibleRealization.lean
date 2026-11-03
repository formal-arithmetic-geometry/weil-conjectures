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
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

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

namespace AlgebraicGeometry.ProEtale.CondensedCoefficientRealization

/-- The literal derived section equivalence for the pulled-back condensed ring.
Source: Stacks 03EK, 05RU; the ambient-category sentence of
cor-coef-verdier-weil-equivariance.proof.md
(blueprint: lem-sf-adic-qbar-constructible-realization). -/
def ambientEquivalence :
    DerivedCategory.{u + 1} (Internal Λ X) ≌ DerivedCategory.{u + 1} (Modules Λ X) := by
  letI : (forward Λ X).IsEquivalence := by unfold forward; infer_instance
  exact (forward Λ X).asEquivalence

/-- Constructibility in section coordinates is the original constructibility predicate
on the internal module reconstructed by the inverse section equivalence. This keeps
the finite stratification and its finite constant models, including the empty scheme.
Source: sk-def-sfb-constructible, final paragraph; Stacks 03EK
(blueprint: lem-sf-adic-qbar-constructible-realization). -/
def sectionConstructible : ObjectProperty (DerivedCategory.{u + 1} (Modules Λ X)) :=
  (constantModelBoundedConstructible Λ X).inverseImage (ambientEquivalence Λ X).inverse

/-- The fixed section functor realizes bounded constructible complexes without changing
ambient morphisms. Its image is precisely sectionConstructible, independently of any
choice of a coefficient-field representative.
Source: sk-def-sfb-constructible and Stacks 03EK, 05RU
(blueprint: lem-sf-adic-qbar-constructible-realization).
Proof: the unit of the derived equivalence identifies each reconstructed object with
its original internal module complex. Invariance under isomorphisms identifies the
predicates. Restrict the equivalence to the two full subcategories. -/
def constructibleEquivalence :
    ConstantModelBoundedConstructible Λ X ≌ (sectionConstructible Λ X).FullSubcategory := by
  letI : (constantModelBoundedConstructible Λ X).IsClosedUnderIsomorphisms := by
    classical
    have hlocal (Y : Scheme.{u})
        {M N : Internal Λ Y} (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ Y M) :
        HasFiniteConstantLocalModel Λ Y N := by
      obtain ⟨𝒰, h𝒰⟩ := hM
      refine ⟨𝒰, fun i ↦ ?_⟩
      obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
      exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (𝒰.f i)).mapIso e.symm ≪≫ eP⟩⟩
    have hstrat (Y : Scheme.{u}) {M N : Internal Λ Y} (e : M ≅ N)
        (hM : IsFiniteConstantStratified Λ Y M) : IsFiniteConstantStratified Λ Y N := by
      obtain ⟨S, hS⟩ := hM
      exact ⟨S, fun a ↦ hlocal _
        ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
    let : ObjectProperty.IsClosedUnderIsomorphisms (IsConstantModelConstructible Λ X) :=
      ⟨fun e hM ↦ by
        unfold IsConstantModelConstructible at hM ⊢
        split_ifs at hM ⊢ with hX
        · exact hstrat _ e hM
        · exact fun U hU ↦ hstrat _ ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)⟩
    exact ⟨fun e hK ↦ ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e hK.1,
      fun n ↦ ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK.2 n)⟩⟩
  letI : (sectionConstructible Λ X).IsClosedUnderIsomorphisms := by
    unfold sectionConstructible
    infer_instance
  apply (ambientEquivalence Λ X).congrFullSubcategory
  funext K
  apply propext
  exact ((constantModelBoundedConstructible Λ X).prop_iff_of_iso
    ((ambientEquivalence Λ X).unitIso.app K)).symm

/-- Forgetting the constructible restriction gives the fixed derived section functor
on both objects and morphisms, not merely an abstract equivalent presentation.
Source: Stacks 03EK, 05RU; cor-coef-verdier-weil-equivariance.proof.md, paragraph 2
(blueprint: lem-sf-adic-qbar-constructible-realization).
Proof: congrFullSubcategory uses the original functor and the full-subcategory lift;
forgetting that lift is definitionally the original composite. -/
theorem constructibleEquivalence_forget :
    (constructibleEquivalence Λ X).functor ⋙ (sectionConstructible Λ X).ι =
      (constantModelBoundedConstructible Λ X).ι ⋙ forward Λ X := rfl

/-- The evaluation-compatible section realization works over every commutative
condensed ring, including both field coefficients used by Weil equivariance.

Source: current cor-coef-verdier-weil-equivariance.proof.md, paragraph 2;
Stacks 03EK, 05RU, 08J9--08JB
(blueprint: lem-sf-adic-qbar-constructible-realization).

Proof: localize the additive section equivalence, retaining its shift comparison
and triangulated structure. Restrict it using the unit isomorphism and the existing
constant-model constructibility predicate. The module-object/ringed-site comparison
supplies the normalized tensor and natural internal-Hom isomorphisms together with
their evaluation identity. The construction uses the coefficient ring itself and
needs no choice of a finite coefficient-field representative. -/
theorem condensed_constructible_realization :
    (forward Λ X).IsEquivalence ∧
    (∃ s : (forward Λ X).CommShift ℤ, letI := s; (forward Λ X).IsTriangulated) ∧
    Nonempty (ConstantModelBoundedConstructible Λ X ≌
      (sectionConstructible Λ X).FullSubcategory) ∧
    Nonempty (ClosedPresentation Λ X) := by
  have hEquiv : (forward Λ X).IsEquivalence := by unfold forward; infer_instance
  let := hEquiv
  refine ⟨hEquiv, ?_, ⟨constructibleEquivalence Λ X⟩,
    adic_ambient_hom_evaluation_comparison Λ X⟩
  dsimp only [forward]
  exact ⟨inferInstance, inferInstance⟩

/-- The algebraic-closure coefficient realization uses the condensed ring itself,
pulled back from the pro-etale point. Its ambient section functor is an exact
equivalence, its bounded constructible restriction is the fixed full subcategory,
and its K-flat tensor and natural internal-Hom comparison preserve evaluation.

Source: current cor-coef-verdier-weil-equivariance.proof.md, paragraph 2;
Stacks 03EK, 05RU, 08J9--08JB
(blueprint: lem-sf-adic-qbar-constructible-realization).

Proof: apply the internal-module/ringed-site derived comparison to the actual
condensed coefficient ring. Retain its normalized tensor and Hom isomorphisms and
evaluation equation. The functor is the localization of the additive section
equivalence, so it preserves shifts and distinguished triangles and is an equivalence.
The same exact section equivalence restricts to the full constructible categories
by constructibleEquivalence. All constructions precede any Weil structure; thus the
comparison applies to the Frobenius structure itself in the ambient category. -/
theorem adic_qbar_constructible_realization (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) :
    let Λ := Profinite.padicAlgClRingObj ℓ
    (forward Λ X).IsEquivalence ∧
    (∃ s : (forward Λ X).CommShift ℤ, letI := s; (forward Λ X).IsTriangulated) ∧
    Nonempty (ConstantModelBoundedConstructible Λ X ≌
      (sectionConstructible Λ X).FullSubcategory) ∧
    Nonempty (ClosedPresentation Λ X) := by
  exact condensed_constructible_realization (Profinite.padicAlgClRingObj ℓ) X

end AlgebraicGeometry.ProEtale.CondensedCoefficientRealization
