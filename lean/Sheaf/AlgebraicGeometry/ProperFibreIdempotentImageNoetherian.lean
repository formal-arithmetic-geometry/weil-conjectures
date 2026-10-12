/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.FormalFunctionsStalk
import Sheaf.AlgebraicGeometry.NilpotentBaseChangeIdempotents
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # The locally Noetherian part of proper-fibre idempotent lifting

Source: Stacks Project, Tag 0G7X, Noetherian case.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Idempotents on a proper fibre over a locally Noetherian base lift to sections
near the base point. Source: Stacks Project, Tag 0G7X, Noetherian part of the proof.

Proof: Let A be the local ring at s, m its maximal ideal, and M the stalk of f_* O_X.
The ring A is Noetherian, hence m is finitely generated. On the infinitesimal fibres
X_n over A/m^(n+1), nilpotent base change lifts e uniquely to idempotents e_n.
Uniqueness implies that the e_n restrict compatibly, and e_0 corresponds to e.
Formal functions for O_X identifies the completion of M with the inverse limit of
these section modules. Let z in the completion correspond to (e_n). The quotient of
the completion by m is M/mM, so choose x in M with the same quotient class as z.
The component on the ordinary fibre is A-linear and m kills its target; consequently
x and z have the same fibre image, namely e. Represent x by a section t over f⁻¹(U)
for a neighbourhood U of s. The formal-functions germ formula identifies its fibre
restriction with e. The first infinitesimal fibre and the usual fibre are identified
by A/m = κ(s) and symmetry of the pullback, preserving their projections to X.
(blueprint: lem-weil-pbc-stein-fibre-idempotent-image-noetherian) -/
theorem proper_fibre_idempotent_image_noetherian
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [IsLocallyNoetherian S] (s : S)
    (e : Γ(f.fiber s, ⊤)) (he : IsIdempotentElem e) :
    ∃ (U : S.Opens), s ∈ U ∧
      ∃ (h : (⊤ : (f.fiber s).Opens) ≤ (f.fiberι s) ⁻¹ᵁ (f ⁻¹ᵁ U))
        (t : Γ(X, f ⁻¹ᵁ U)),
        (f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤ h t = e := by
  sorry


end AlgebraicGeometry
