module

public import Sheaf.RingTheory.SupportedHomogeneousDivision

/-! # Degree prefixes and essential restriction of monotone diagrams

Source: Bierstone--Milman, Invent. Math. 128 (1997), section 7, (7.2)(2),
section 8, pp.273--275, and its application in Theorem 9.6, p.282.
The combinatorial preservation argument is written out in the DAG.
(blueprint: lem-trf-monotone-prefix-essential-restriction)
-/

@[expose] public section

set_option autoImplicit false

namespace MonomialDiagram

/-- The essential variables carry the order inherited from the original variables.
Source: Bierstone--Milman, section 8 and Theorem 9.6, p.282.
(blueprint: lem-trf-monotone-prefix-essential-restriction). -/
instance essentialVariablesLinearOrder {σ ι : Type} [LinearOrder σ]
    (a : ι → σ →₀ ℕ) : LinearOrder (EssentialVariables a) :=
  inferInstanceAs (LinearOrder {j : σ // ∃ i : ι, a i j ≠ 0})

/-- Degree prefixes and restriction to essential variables preserve monotone diagrams,
ordered minimal vertices, and their quotient supports. Each prefix uses its own
set of essential variables. `Finsupp.embDomain (Function.Embedding.subtype _)`
is extension by zero from those variables.

Source: Bierstone--Milman, section 7, (7.2)(2), section 8, and Theorem 9.6, p.282;
agent's finite-coordinate argument
(blueprint: lem-trf-monotone-prefix-essential-restriction).

Proof plan (the seven steps of the DAG):
1. For x in D, choose a least-degree element among the finitely many elements
of D below x. It is minimal and therefore a listed vertex. Conversely every
exponent above a vertex belongs to D by additivity.
2. The degree bound retains an initial segment of the vertex indices. Its generated
diagram is additive, and precisely these vertices remain minimal and ordered.
Every earlier vertex of a retained vertex is retained, so quotient supports agree
(def-trf-supported-homogeneous-division).
3. A whole-coordinate move T is additive and preserves degree. For a retained
vertex a_i, choose a vertex a_h below T(a_i). Its degree is at most that of a_i,
so it is retained; T(a_i+b) is above a_h. This proves prefix monotonicity.
4. If an essential variable p precedes an unused variable v, move the positive
p-coordinate of a vertex to v. A vertex below the result vanishes at v and p,
and hence is strictly below the original vertex, contradicting minimality.
5. All vertices vanish outside the essential variables. Restriction and zero
extension preserve and reflect their coordinate comparisons and preserve degrees.
The first coordinate where two vertices differ is essential, so their degree-lex
order is preserved. The restricted generated diagram is additive and has exactly
these ordered minimal vertices.
6. Extension by zero identifies membership of the restricted diagram with
membership in D and commutes with the required coordinate moves. The same
comparison applied to each earlier vertex gives the quotient-support equality
(def-trf-supported-homogeneous-division), and membership gives the complement equality.
7. Apply steps 4--6 to each prefix from steps 2--3, using its own essential
variables. An empty vertex family generates the empty diagram and has no quotient
supports; its restriction has singleton complement. The full diagram has sole
vertex zero, empty essential set, singleton quotient support, and empty complement.
These two cases exhaust dimension zero; all moves there are vacuous. -/
theorem monotone_prefix_essential_restriction (n s : ℕ) (D : Set (Fin n →₀ ℕ))
    (a : Fin s → Fin n →₀ ℕ) (hD : IsMonotone D) (ha : IsOrderedVertexFamily D a) :
    (∀ u : ℕ,
      IsMonotone (generated (prefixVertices a u)) ∧
      IsOrderedVertexFamily (generated (prefixVertices a u)) (prefixVertices a u) ∧
      ∀ i : {i : Fin s // (a i).degree ≤ u},
        quotientSupport (prefixVertices a u) i = quotientSupport a i.val) ∧
    ((∀ p v : Fin n, p < v → (∃ i : Fin s, a i p ≠ 0) →
        ∃ i : Fin s, a i v ≠ 0) ∧
      IsMonotone (generated (essentialVertices a)) ∧
      IsOrderedVertexFamily (generated (essentialVertices a)) (essentialVertices a) ∧
      (∀ i : Fin s, (essentialVertices a i).degree = (a i).degree) ∧
      (∀ i : Fin s, quotientSupport (essentialVertices a) i =
        {b : EssentialVariables a →₀ ℕ |
          Finsupp.embDomain (Function.Embedding.subtype _) b ∈ quotientSupport a i}) ∧
      (generated (essentialVertices a))ᶜ =
        {g : EssentialVariables a →₀ ℕ |
          Finsupp.embDomain (Function.Embedding.subtype _) g ∉ D}) ∧
    (∀ u : ℕ,
      (∀ p v : Fin n, p < v →
        (∃ i : {i : Fin s // (a i).degree ≤ u}, prefixVertices a u i p ≠ 0) →
        ∃ i : {i : Fin s // (a i).degree ≤ u}, prefixVertices a u i v ≠ 0) ∧
      IsMonotone (generated (essentialVertices (prefixVertices a u))) ∧
      IsOrderedVertexFamily (generated (essentialVertices (prefixVertices a u)))
        (essentialVertices (prefixVertices a u)) ∧
      (∀ i : {i : Fin s // (a i).degree ≤ u},
        (essentialVertices (prefixVertices a u) i).degree = (prefixVertices a u i).degree) ∧
      (∀ i : {i : Fin s // (a i).degree ≤ u},
        quotientSupport (essentialVertices (prefixVertices a u)) i =
          {b : EssentialVariables (prefixVertices a u) →₀ ℕ |
            Finsupp.embDomain (Function.Embedding.subtype _) b ∈
              quotientSupport (prefixVertices a u) i}) ∧
      (generated (essentialVertices (prefixVertices a u)))ᶜ =
        {g : EssentialVariables (prefixVertices a u) →₀ ℕ |
          Finsupp.embDomain (Function.Embedding.subtype _) g ∉
            generated (prefixVertices a u)}) := by
  sorry

end MonomialDiagram
