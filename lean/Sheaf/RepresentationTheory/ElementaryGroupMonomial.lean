module

public import Mathlib.Data.Complex.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RepresentationTheory.Induced
public import Mathlib.RepresentationTheory.Irreducible
public import WeilConjectures.Mathlib.RepresentationTheory.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Sheaf.RepresentationTheory.NormalCommutingWeightInduction
import Sheaf.RepresentationTheory.FiniteGroupInductionCalculus

/-! # Monomiality for finite nilpotent and elementary groups

Source: the agent-written representation argument in the accepted DAG, motivated by
Travaux de Gabber, Exposé X, Proposition 1.2, printed p.138, before equation (5)
(blueprint: lem-per-elementary-group-monomial).
Gabber provides context only; Serre, Part II, section 8.5, Theorem 16 is still WANTED.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

namespace Representation

/-- Every nonzero irreducible complex representation of a finite nilpotent group is induced
from a character of a subgroup. The same holds for an elementary group presented as the
product of a cyclic group of order prime to p and a group of order p^a.

Source: the agent-written argument attached to Travaux de Gabber, Exposé X, Proposition 1.2,
printed p.138, before equation (5), context only
(blueprint: lem-per-elementary-group-monomial).

`Group.IsNilpotent` means that the upper central series reaches the whole group; the theorem
`Group.nilpotent_iff_finite_ascending_central_series` identifies this with the stated finite
central-series condition. `ofCharacter χ ℂ` is exactly the line with action χ(k)z.
Mathlib's quotient induction has the node's generator [g] ⊗ z represented by
`IndV.mk K.subtype (ofCharacter χ ℂ) g⁻¹ z`. Inversion of that index turns its coinvariant
relation into [gk] ⊗ z = [g] ⊗ χ(k)z and its right-inverse action into left translation.

Proof:
1. Induct strongly on the positive dimension, simultaneously over all finite nilpotent
groups. In dimension one choose a nonzero w and write rho(n)w = lambda(n)w. The action laws
give a character. Take K = N; the maps [n] ⊗ z ↦ z rho(n)w and zw ↦ [1] ⊗ z are inverse.
2. In larger dimension some operator is nonscalar, since otherwise every line is invariant.
Choose the first central-series term N_j containing such an x. The previous term H acts
by scalars. The subgroup A = H<x> is normal because nxn⁻¹ lies in Hx. Its operators commute
and include the nonscalar operator rho(x).
3. Use `lem-weil-complex-algebraically-closed` and
`lem-per-normal-commuting-weight-induction`. There are at least two nonzero weights, since
one weight would make every operator of A scalar. A weight space U is an irreducible
representation of its stabilizer T, W is induced from U, and 0 < dim U < dim W.
4. Intersect the central series with T to see that T is nilpotent. Apply the dimension
induction to U, obtaining K ≤ T and a character lambda with U induced from its line.
5. Induce that equivalence by [n] ⊗ u ↦ [n] ⊗ f(u). Use the induction-in-stages equivalence
of `lem-per-finite-group-induction-calculus` to identify the resulting representation with
Ind_K^N of the line, completing the induction.
6. For E isomorphic to C × P, `lem-per-finite-prime-power-central-series` supplies a central
series P_i of P. The series 1 ≤ C × 1 ≤ C × P_1 ≤ ... ≤ C × P_c is central because C is
cyclic and [(c,p),(c',q)] = (1,[p,q]). Transport it along the group equivalence and use the
first assertion. For c = 0 the series is just 1 ≤ C; this includes a = 0 and trivial factors.
-/
theorem nilpotent_and_elementary_monomial :
    (∀ (N : Type u) [Group N] [Finite N] [Group.IsNilpotent N]
      (W : Type t) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
      (ρ : Representation ℂ N W) [IsIrreducible ρ],
      ∃ (K : Subgroup N) (χ : K →* ℂˣ),
        Nonempty (Equiv ρ (ind K.subtype (ofCharacter χ ℂ)))) ∧
    (∀ (E : Type u) [Group E] [Finite E]
      (C : Type v) [Group C] [Finite C] [IsCyclic C]
      (P : Type w) [Group P] [Finite P] (p a : ℕ),
      p.Prime → Nat.Coprime (Nat.card C) p → Nat.card P = p ^ a →
      (E ≃* C × P) →
      ∀ (W : Type t) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
        (ρ : Representation ℂ E W) [IsIrreducible ρ],
        ∃ (K : Subgroup E) (χ : K →* ℂˣ),
          Nonempty (Equiv ρ (ind K.subtype (ofCharacter χ ℂ)))) := by
  sorry

end Representation
