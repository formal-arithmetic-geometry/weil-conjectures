/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
import WeilConjectures.AlgebraicGeometry.IsomorphismFieldTransport

/-! # Normalized identity pullback units

Source: the identity paragraph of prop-sf-pf-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
namespace WeilConjectures

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}

/-- Identity inverse image is fully faithful at the three higher coefficient stages.
Source: current blueprint prop-sf-pf-coherence, identity paragraph
(blueprint: lem-sf-projection-identity-pullback-units).
Proof: specialize isomorphismFieldTransport to the identity of each finite-type
space. Its integral, rational and common-stage clauses give equivalences for the
specified canonical pullbacks. Use the three pullback-normalization fields of S
to identify its supplied functors with these canonical functors. Equivalences are
full and faithful. The transport theorem supplies the residue invertibility data
from the fixed prime-to-characteristic coefficient convention; no separatedness,
nonemptiness or extra hypothesis on the objects is used. -/
theorem projectionIdentity_pullbackUnits (S : SixFunctorOperationDatum D C E n hn) :
    (∀ X : SixFunctorSpace D,
      (S.higher.integral.pull (𝟙 X)).Full ∧ (S.higher.integral.pull (𝟙 X)).Faithful) ∧
    (∀ X : SixFunctorSpace D,
      (S.higher.rational.pull (𝟙 X)).Full ∧ (S.higher.rational.pull (𝟙 X)).Faithful) ∧
    (∀ X : SixFunctorSpace D,
      (S.closure.commonStage.pull (𝟙 X)).Full ∧
        (S.closure.commonStage.pull (𝟙 X)).Faithful) := by
  classical
  have h (X : SixFunctorSpace D) :
      ((S.higher.integral.pull (𝟙 X)).Full ∧
        (S.higher.integral.pull (𝟙 X)).Faithful) ∧
      ((S.higher.rational.pull (𝟙 X)).Full ∧
        (S.higher.rational.pull (𝟙 X)).Faithful) ∧
      ((S.closure.commonStage.pull (𝟙 X)).Full ∧
        (S.closure.commonStage.pull (𝟙 X)).Faithful) := by
    let : X.obj.left.Over (Spec (.of D.k)) := ⟨X.obj.hom⟩
    have : LocallyOfFiniteType (X.obj.left ↘ Spec (.of D.k)) := X.property.1
    have : QuasiCompact (X.obj.left ↘ Spec (.of D.k)) := X.property.2
    obtain ⟨i, j, ht⟩ :=
      isomorphismFieldTransport D C.l C.different C.Qbar (𝟙 X.obj.left)
    have hij : j = i := Subsingleton.elim _ _
    subst j
    let := i
    obtain ⟨hX, hY, hstage, _, hcommon⟩ := ht
    obtain ⟨T⟩ := (hstage E).1
    obtain ⟨_, _, _, U, _⟩ := hcommon
    have := T.integralEquivalence
    have := T.rationalEquivalence
    have := U.some.equivalence
    refine ⟨?_, ?_, ?_⟩
    · rw [S.higher.integralPullback (𝟙 X)]
      exact ⟨inferInstanceAs ((constructibleIntegralPullback C.l E (𝟙 X.obj.left)).Full),
        inferInstanceAs ((constructibleIntegralPullback C.l E (𝟙 X.obj.left)).Faithful)⟩
    · rw [S.higher.rationalPullback (𝟙 X)]
      exact ⟨inferInstanceAs ((rationalDerivedPullback C.l E (𝟙 X.obj.left)).Full),
        inferInstanceAs ((rationalDerivedPullback C.l E (𝟙 X.obj.left)).Faithful)⟩
    · rw [S.closure.commonStagePullback (𝟙 X)]
      exact ⟨inferInstanceAs ((commonStageDerivedPullback C.l C.Qbar (𝟙 X.obj.left)).Full),
        inferInstanceAs ((commonStageDerivedPullback C.l C.Qbar (𝟙 X.obj.left)).Faithful)⟩
  exact ⟨fun X ↦ (h X).1, fun X ↦ (h X).2.1, fun X ↦ (h X).2.2⟩

end WeilConjectures
