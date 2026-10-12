/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.FormalFibreCohomology
import Sheaf.AlgebraicGeometry.NilpotentBaseChangeIdempotents

/-! # One-step lifting of infinitesimal-fibre idempotents -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Restriction across one infinitesimal-fibre transition uniquely lifts idempotents.
Source: Stacks Project, Tags 0G7X, 09ZU, 04EX and 00EE.
(blueprint: lem-weil-pbc-formal-fibre-transition-idempotents)

Proof: Write A = O_(S,s) and m = its maximal ideal. The quotient map
A/m^(n+2) → A/m^(n+1) has kernel J, the image of m^(n+1). Its square is zero:
2(n+1) ≥ n+2, so m^(2(n+1)) maps to zero in A/m^(n+2).
The quotient by J is canonically A/m^(n+1), with the quotient map identified with
factorPow. Pullback pasting identifies the base change of X_(n+1) along this
quotient with X_n, and its projection with formalFibreTransition f s n.
Apply nilpotent_baseChange_idempotents with N = 2 and transport along this
identification. This gives existence and uniqueness among idempotent sections,
including 0 and 1 and the unique section of an empty fibre; it makes no claim
that all global sections lift. -/
theorem formalFibreTransition_idempotents {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (n : ℕ) (e : Γ(formalFibre f s n, ⊤)) (he : IsIdempotentElem e) :
    ∃! e' : {a : Γ(formalFibre f s (n + 1), ⊤) // IsIdempotentElem a},
      (formalFibreTransition f s n).appTop.hom e'.val = e := by
  sorry

end AlgebraicGeometry
