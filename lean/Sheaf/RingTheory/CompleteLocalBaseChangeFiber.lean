/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Quotient
import Sheaf.RingTheory.CompleteLocalQuotient

/-!
# Complete local base change along a surjection and its closed fibre

Source: Stacks Project, More on Algebra, Tag 07NR, final base change;
Algebra, Tags 00DF and 0325.
(blueprint: lem-weil-pbc-complete-local-base-change-fiber)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra

/-- Base change of a complete local algebra along a surjective local map remains
complete local, and preserves an identified closed fibre compatibly with the new base.

Source: Stacks Project, More on Algebra, Tag 07NR (lemma-lift-fs), final base change,
with the quotient descriptions from Algebra 00DF and completeness from Algebra 0325.
(blueprint: lem-weil-pbc-complete-local-base-change-fiber)

Proof: Let I = ker(R → A). Surjectivity identifies A with R/I, and the tensor
quotient isomorphism identifies C = T ⊗[R] A with T/IT, taking t ⊗ 1 to t mod IT.
Since the map R → T is local and I lies in m_R, IT lies in m_T. Thus this quotient
is nonzero, Noetherian, local, and complete, and its maximal ideal is the image of
m_T (Algebra 0325). Transport these assertions to C. For a in m_A choose r in m_R
mapping to a: this is possible because a surjective local map maps its maximal
ideal onto the target maximal ideal. Its image in C lies in m_C, proving locality
of A → C. Under C = T/IT, the ideal m_A C is the image of m_R T, because the same
surjective-map calculation gives q(m_R) = m_A and I is contained in m_R. The
successive-quotient isomorphism therefore identifies C/m_A C with T/m_R T.
Compose it with e. For any a in A lift a to r in R; the assumed compatibility
of e gives the image of a under A → E. This proves that the resulting ring
isomorphism is an A-algebra isomorphism. No flatness, regularity or formal
smoothness is required. If I = 0 the quotient is T itself; if m_R = 0 then A = R
and the fibre is T, so the construction also covers these boundary cases. -/
theorem complete_local_baseChange_closedFiber
    (R : Type w) (A : Type u) (T : Type w) (E : Type v)
    [CommRing R] [CommRing A] [CommRing T] [CommRing E]
    [IsLocalRing R] [IsLocalRing A] [IsLocalRing T]
    [IsNoetherianRing T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    [Algebra R A] [Algebra R T] [Algebra A E]
    [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap R T)]
    (hq : Function.Surjective (algebraMap R A))
    (e : (T ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R T)) ≃+* E)
    (he : ∀ r : R,
      e (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R T))
        (algebraMap R T r)) = algebraMap A E (algebraMap R A r)) :
    letI : Algebra A (T ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
    ∃ hlocal : IsLocalRing (T ⊗[R] A),
      IsNoetherianRing (T ⊗[R] A) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (T ⊗[R] A)) (T ⊗[R] A) ∧
      IsLocalHom (algebraMap A (T ⊗[R] A)) ∧
      (IsLocalRing.maximalIdeal T).map (algebraMap T (T ⊗[R] A)) =
        IsLocalRing.maximalIdeal (T ⊗[R] A) ∧
      Nonempty (((T ⊗[R] A) ⧸
        (IsLocalRing.maximalIdeal A).map (algebraMap A (T ⊗[R] A))) ≃ₐ[A] E) := by
  sorry

end Algebra
