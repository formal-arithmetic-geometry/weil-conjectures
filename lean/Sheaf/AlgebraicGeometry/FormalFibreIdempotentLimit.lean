/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.FormalFibreCohomology
import Sheaf.AlgebraicGeometry.NilpotentBaseChangeIdempotents

/-! # Compatible lifting of formal-fibre idempotents

Source: Stacks Project, Tag 0G7X, the infinitesimal lifting step.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An idempotent on the zeroth formal fibre extends to a compatible system of sections.
Source: Stacks Project, Tag 0G7X, lines 8133--8146; Tags 09ZU, 04EX and 00EE.
(blueprint: lem-weil-pbc-formal-fibre-idempotent-limit)

Proof: Put A = O_(S,s) and m = its maximal ideal. The map from X_0 to X_n is
base change of A/m^(n+1) to A/m. Its quotient ideal m/m^(n+1) has (n+1)st power
zero. Identify this pullback with X_0 by pullback pasting and the quotient-ring
isomorphism. Nilpotent base change therefore gives a unique idempotent e_n mapping
to e. A transition pulls an idempotent back to an idempotent. Its composite with
restriction to X_0 is restriction to X_0, so uniqueness implies that e_(n+1)
restricts to e_n. The resulting compatible family is a section of the inverse
system. The concrete limit of modules identifies compatible families with elements
of the limit; its zeroth projection is e. No properness or Noetherian hypothesis
is needed for this step. -/
theorem formalFibre_idempotent_limit {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (e : Γ(formalFibre f s 0, ⊤)) (he : IsIdempotentElem e) :
    ∃ v : ↥(limit (formalFibreSectionsSystem f s)),
      (limit.π (formalFibreSectionsSystem f s) (op 0)) v = e := by
  sorry

end AlgebraicGeometry
