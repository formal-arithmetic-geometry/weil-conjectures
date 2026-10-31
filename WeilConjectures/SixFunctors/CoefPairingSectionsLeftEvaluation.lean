/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefPairingExceptionalTests

/-! # Finite evaluation of sections left adjoints

Source: prop-coef-integral-dualizing, second proof paragraph; Stacks 07A6 and 0941.
(blueprint: lem-coef-pairing-sections-left-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option linter.unusedVariables false in
/-- Evaluation of a sections left adjoint is finite scalar extension followed by
the finite constant sheaf left adjoint. The statement is independent of any
compactification, pairing frame, proper tensor or projection mate.

Source: prop-coef-integral-dualizing, paragraph 2, mapping-complex adjunction;
Stacks 07A6 and 0941.
(blueprint: lem-coef-pairing-sections-left-evaluation).

Proof: construct the ordinary left adjoint to quotient-linear sections by constant
sheafification of a module tower, followed by scalar extension to the quotient
coefficient system. Resolve the input tower by flat-term K-flat complexes and
localize this scalar extension. Its derived adjunction is with the fixed sections
functor: scalar restriction followed by derived sections; the usual scalar-change
acyclicity comparison identifies the right-derived composite, so no assertion
that quotient restriction preserves K-injectives is needed. At a finite vertex
the same construction is derived extension from the completed scalar ring to the
quotient followed by the finite constant sheaf functor. Termwise evaluation of the
constant and scalar-extension complexes gives the identity finite construction
on K-flat representatives, and hence the natural derived comparison for every
scalar tower. Compare L and the constructed system left adjoint, and compare Lf
and the constructed finite left adjoint, using uniqueness of left adjoints to
the specified right functors. Whiskering the resulting isomorphisms gives the
displayed isomorphism. This proof does not use conservativity of all evaluations,
which would not detect equalities of natural transformations. It applies to
unbounded scalar complexes, q = 0, the empty scheme and zero objects. -/
theorem coefPairing_sections_left_evaluation (W : Scheme.{u})
    (L : coefPairingDerived l E ⥤ coefficientSequenceDerived.{u, u} l E W)
    (adj : L ⊣ coefPairingSections l E W) (q : ℕ)
    (Lf : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) ⥤
      normalizedDVRDerived.{u, u} l E W q)
    (level : Lf ⊣ coefPairingFiniteSections l E W q) :
    Nonempty (L ⋙ coefficientSequenceDerivedEvaluation l E W q ≅
      coefPairingDerivedEvaluation l E q ⋙ Lf) := by sorry

end WeilConjectures
