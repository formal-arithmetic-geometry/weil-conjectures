module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Telescoping criterion for a homogeneous submodule

Source: Bierstone--Milman, Invent. Math. 128 (1997), proof of Theorem 8.1 after
Lemma 8.5, printed p. 275; the arbitrary-submodule formulation isolated in the DAG
(blueprint: lem-trf-homogeneous-coordinate-lifting-criterion).
-/

@[expose] public section

universe u

namespace MvPolynomial

/-- Successive coordinate-face lifting forces a positive homogeneous component to be full.
The paper's variable `Y_{j+1}` is `X j` for `j : Fin n`; setting the first `r` variables
zero is `aeval (fun i ↦ if i.val < r then 0 else X i)`. Tail polynomial rings are the
existing subalgebras `supported A {i | r ≤ i.val}`.

Source: Bierstone--Milman, Invent. Math. 128 (1997), proof of Theorem 8.1 after
Lemma 8.5, printed p. 275; arbitrary-submodule formulation in the DAG
(blueprint: lem-trf-homogeneous-coordinate-lifting-criterion).

Proof plan, using the finite monomial expansion of def-weil-pbc-mv-polynomial-ring:
1. The difference of two consecutive coordinate restrictions keeps precisely the
monomials whose first nonzero exponent occurs at the current variable. It is homogeneous,
supported on the tail variables, and divisible by the current variable.
2. Induct strongly on the face index r. At r = 0 the hypothesized lift is already P.
3. For a lift Q at face r, each earlier restriction difference belongs to S by induction.
Their sum is Q minus its r-th restriction, so subtracting this sum from Q shows P lies in S.
4. Apply this to the consecutive restriction differences of T. Their sum is T minus
its restriction at all variables zero. This last restriction vanishes in positive degree.
Thus every T belongs to S and the two submodules are equal. For n = 0 the positive
homogeneous component and the sum are both zero; the zero ring needs no special assumption.
-/
theorem homogeneous_coordinate_lifting_criterion
    {A : Type u} [CommRing A] (n ℓ : ℕ) (hℓ : 0 < ℓ)
    (S : Submodule A (MvPolynomial (Fin n) A))
    (hS : S ≤ homogeneousSubmodule (Fin n) A ℓ)
    (hLift : ∀ (r : Fin n) (P : MvPolynomial (Fin n) A),
      P ∈ homogeneousSubmodule (Fin n) A ℓ →
      P ∈ supported A {i : Fin n | r.val ≤ i.val} →
      X r ∣ P → ∃ Q ∈ S,
        aeval (fun i : Fin n ↦ if i.val < r.val then 0 else X i) Q = P) :
    (∀ (r : Fin n) (P : MvPolynomial (Fin n) A),
      P ∈ homogeneousSubmodule (Fin n) A ℓ →
      P ∈ supported A {i : Fin n | r.val ≤ i.val} → X r ∣ P → P ∈ S) ∧
    S = homogeneousSubmodule (Fin n) A ℓ ∧
    ∀ (T : MvPolynomial (Fin n) A), T ∈ homogeneousSubmodule (Fin n) A ℓ →
      (∀ j : Fin n,
        (aeval (fun i : Fin n ↦ if i.val < j.val then 0 else X i) T -
          aeval (fun i : Fin n ↦ if i.val < j.val + 1 then 0 else X i) T) ∈ S ∧
        (aeval (fun i : Fin n ↦ if i.val < j.val then 0 else X i) T -
          aeval (fun i : Fin n ↦ if i.val < j.val + 1 then 0 else X i) T) ∈
            supported A {i : Fin n | j.val ≤ i.val} ∧
        (X j : MvPolynomial (Fin n) A) ∣
          (aeval (fun i : Fin n ↦ if i.val < j.val then 0 else X i) T -
            aeval (fun i : Fin n ↦ if i.val < j.val + 1 then 0 else X i) T)) ∧
      T = ∑ j : Fin n,
        (aeval (fun i : Fin n ↦ if i.val < j.val then 0 else X i) T -
          aeval (fun i : Fin n ↦ if i.val < j.val + 1 then 0 else X i) T) := by
  sorry

end MvPolynomial
