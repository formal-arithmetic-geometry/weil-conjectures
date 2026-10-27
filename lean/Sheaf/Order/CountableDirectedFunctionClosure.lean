module

public import Mathlib.Data.Set.Countable
public import Mathlib.Order.Directed

/-!
# Countable directed enlargement closed under a function

Source: Stacks Project, Algebra, Tag 059W, proof of lemma-ML-countable-colimit,
the successive countable enlargements and their union
(blueprint: lem-trf-countable-directed-function-closure).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Set

/-- Every countable subset of a nonempty directed partial order has a nonempty countable
directed superset closed under any prescribed self-map, without monotonicity of that map.

Source: Stacks Project, Algebra, Tag 059W, proof of lemma-ML-countable-colimit,
abstracting the successive countable enlargements and their union
(blueprint: lem-trf-countable-directed-function-closure).

Proof:
1. Choose an index i_* and, for every pair i,j, an upper bound b(i,j). Starting with
   T_0 = S ∪ {i_*}, recursively put T_(n+1) = T_n ∪ s(T_n) ∪ b(T_n × T_n).
   Each stage contains the preceding stage, hence T_n ⊆ T_m whenever n ≤ m.
2. Singletons are countable in the sense of def-sfb-countable-set. By the binary-union
   clause of lem-trf-countable-unions, T_0 is countable. If T_n is countable, write its
   s-image as the union of singletons over T_n, and its b-image as an iterated union
   of singletons over T_n and T_n. The restricted-union clause and two binary unions
   prove countability of T_(n+1). The sequence-union clause makes J = ⋃ n, T_n countable.
3. The initial stage ensures S ⊆ J and i_* ∈ J, including when S is empty. Any i ∈ J
   lies in some T_n, so s(i) lies in T_(n+1), proving s(J) ⊆ J without monotonicity.
4. If i ∈ T_n and j ∈ T_m, both belong to T_(max n m). Thus b(i,j) belongs to the
   next stage and hence to J, and is an upper bound for i,j inside J.
-/
theorem exists_countable_directed_superset_closed
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (s : I → I) (S : Set I) (hS : S.Countable) :
    ∃ J : Set I, J.Countable ∧ J.Nonempty ∧ S ⊆ J ∧ s '' J ⊆ J ∧ DirectedOn (· ≤ ·) J := by
  sorry

end Set
