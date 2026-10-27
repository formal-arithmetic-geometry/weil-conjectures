module

public import Sheaf.RingTheory.SupportedHomogeneousDivision
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.FiniteType

/-! # A finite test for supported homogeneous division

Source: Bierstone--Milman, Invent. Math. 128 (1997), Theorem 8.1,
Definition 8.3 and Remarks 8.4, pp.273--275; ILO VIII 2.3.11--2.3.13.
(blueprint: lem-trf-initial-diagram-stabilization)
-/

@[expose] public section

universe u

namespace MonomialDiagram

/-- A monotone diagram has a bound uniform over all commutative coefficient rings.
The four clauses cover the original diagram, each degree prefix, restriction to
its essential variables, and the essential-variable restriction of each prefix.

Source: Bierstone--Milman, Theorem 8.1 and its application in Theorem 9.6;
ILO VIII 2.3.11--2.3.13 (blueprint: lem-trf-initial-diagram-stabilization).

Proof plan (the DAG's ten steps):
1. Degree-t monomials form a finite basis. Assigning each diagram exponent to
its first dividing vertex identifies their indices with those of `P(t)`
(def-weil-pbc-free-module). For n = 0 take bound zero.
2. Put d = max of zero and all vertex degrees, M = max(1,d), and
b = d + n*(M-1) + 1. The exceptional-box bound of
lem-trf-monotone-diagram-face-exceptions implies that above b every quotient
or remainder exponent on each coordinate face stays in its support after
adding the first remaining coordinate vector.
3. Setting the first r variables to zero carries a spanning degree-k family
to a spanning family in the remaining variables. Terms whose multiplier has
one of those coordinates positive vanish.
4. Divide a degree-(k+1) polynomial divisible by the first remaining variable
by that variable, express it in the restricted degree-k family, and use step 2
to lift its product into the span of `P(k+1)` (BM Lemma 8.5).
5. Induct on the number of coordinates set to zero. The difference between a
lift and its restriction telescopes into the earlier coordinate cases. Finally
any positive-degree homogeneous polynomial telescopes in the same way, proving
that `P(k+1)` spans.
6. Induct on t-q to propagate spanning from q >= b to every t >= q.
7. The index bijection of step 1 turns a spanning family into a surjective
endomorphism of a finite free module. Over a commutative ring it is bijective
(lem-weil-pbc-finite-module-surjective-endomorphism-bijective, the Orzech theorem).
Thus the indexed family is a basis, including over the zero ring.
8. Test degrees through b and propagate from b. The bases give unique finite
coefficients; grouping them by vertex gives supported quotients and remainder.
Conversely unique division implies spanning in the test degrees.
9. A degree prefix is monotone: moving a vertex coordinate produces a diagram
element divisible by a vertex of no larger degree. Retained vertices have the
same earlier vertices and hence the same quotient supports. Apply steps 1--8.
10. Essential variables form a final segment: otherwise moving a positive
vertex coordinate to an unused later variable contradicts its minimality.
Delete the unused initial coordinates and apply steps 1--8, also separately
for every prefix. Empty prefixes and diagrams with no essential variables
reduce to the n = 0 case. -/
theorem exists_finiteDivisionTest (n s : ℕ) (D : Set (Fin n →₀ ℕ))
    (a : Fin s → Fin n →₀ ℕ) (hD : IsMonotone D) (ha : IsOrderedVertexFamily D a) :
    (∃ b : ℕ, ∀ (A : Type u) (_ : CommRing A), IsFiniteDivisionTest D a A b) ∧
    (∀ d : ℕ, ∃ b : ℕ, ∀ (A : Type u) (_ : CommRing A),
      IsFiniteDivisionTest (generated (prefixVertices a d)) (prefixVertices a d) A b) ∧
    (∃ b : ℕ, ∀ (A : Type u) (_ : CommRing A),
      IsFiniteDivisionTest (generated (essentialVertices a)) (essentialVertices a) A b) ∧
    (∀ d : ℕ, ∃ b : ℕ, ∀ (A : Type u) (_ : CommRing A),
      IsFiniteDivisionTest (generated (essentialVertices (prefixVertices a d)))
        (essentialVertices (prefixVertices a d)) A b) := by
  sorry

end MonomialDiagram
