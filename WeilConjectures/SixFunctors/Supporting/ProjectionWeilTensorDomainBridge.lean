/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.SixFunctors.Supporting.PbcWeilCategory
public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
import all WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.SixFunctors.WfTensorCompletion.WfTensorCompletionFrobenius
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
import all WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct

/-! # Coefficient and constructible-domain bridge for the Weil projection inputs

Source: main-20261015, sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, Weil-equivariance sentence
(blueprint: lem-sf-projection-weil-tensor-domain-bridge).

The coefficient identification, integral and rational tensor comparisons, and operation
outputs below are the clauses of this bridge. No projection map is assumed invertible.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
universe v r w

section TensorTransport
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem comparison_exists
    {A : Type u} {B : Type v} (P : A → Prop) (Q J H : A → B → B → Prop)
    (h : ∃ a, P a ∧ ∀ b c, J a b c ∧ Q a b c)
    (hH : ∀ a, P a → ∀ b c, H a b c) :
    ∃ a, P a ∧ ∀ b c, Q a b c ∧ H a b c := by
  obtain ⟨a, ha, hq⟩ := h
  exact ⟨a, ha, fun b c ↦ ⟨(hq b c).2, hH a ha b c⟩⟩

/-- A functor respects heterogeneous equality once its endpoints agree. -/
private theorem map_heq {C : Type u} [Category C] {D : Type v} [Category D]
    (F : C ⥤ D) {X X' Y Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst hx
  subst hy
  cases h
  rfl

/-- Transport a normalized component using only functor and object equalities. -/
private theorem component_transport
    {A : Type u} [Category A] {B : Type v} [Category B]
    {C : Type r} [Category C] {D : Type w} [Category D]
    (Q : A ⥤ B) (I : B ⥤ D) (J : A ⥤ C) (QA : C ⥤ D)
    (S : A × A ⥤ A) (T : B × B ⥤ B) (F₀ : A ⥤ A) (F : B ⥤ B)
    (hI : Q ⋙ I = J ⋙ QA) (hT : (Q.prod Q) ⋙ T = S ⋙ Q)
    (hF : ∀ M : A, F.obj (Q.obj M) = Q.obj (F₀.obj M))
    (mu₀ : ∀ M N : A, F₀.obj (S.obj (M, N)) ⟶ S.obj (F₀.obj M, F₀.obj N))
    (mu : ∀ M N : B, F.obj (T.obj (M, N)) ⟶ T.obj (F.obj M, F.obj N))
    (hmu : ∀ M N : A, HEq (mu (Q.obj M) (Q.obj N)) (Q.map (mu₀ M N)))
    (M N : A) :
    HEq (I.map (mu (Q.obj M) (Q.obj N))) (QA.map (J.map (mu₀ M N))) := by
  have hs := (congrArg F.obj (Functor.congr_obj hT (M, N))).trans (hF (S.obj (M, N)))
  have hp : (F.obj (Q.obj M), F.obj (Q.obj N)) =
      (Q.obj (F₀.obj M), Q.obj (F₀.obj N)) := Prod.ext (hF M) (hF N)
  have ht := (congrArg T.obj hp).trans (Functor.congr_obj hT (F₀.obj M, F₀.obj N))
  exact (map_heq I hs ht (hmu M N)).trans (Functor.hcongr_hom hI (mu₀ M N))

end TensorTransport

namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Coefficient)

section RationalNormalization
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) (p : A)

end RationalNormalization

section TensorNormalization
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open WfTensorCompletion

attribute [local irreducible] wfRationalTensor wfConstructibleInclusion
  wfRationalTensorPullback wfWeilStructure wfTensorFrobenius
  ScalarLocalization.category ScalarLocalization.preadditive ScalarLocalization.composition
  ScalarLocalization.linear ScalarLocalization.linearOriginal
  pbcIntegralLinear pbcCompletedDerivedLinear pbcCompletedModulesLinear
  wfPullbackCompletion proEtaleCanonicalTensorComparison pbcCompletedScalarSections
  wfCompletionObj intrinsicCompletion intrinsicCompletionUnit

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (.of D.k₀))) [IsSeparated X₀.hom]
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)

section TensorComponents
attribute [local semireducible] wfRationalTensor ScalarLocalization.category

end TensorComponents

attribute [local semireducible] wfWeilStructure wfTensorFrobenius

end TensorNormalization

end WeilConjectures
