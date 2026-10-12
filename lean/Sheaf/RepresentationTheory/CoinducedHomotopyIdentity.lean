/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker H1
-/
module

public import Sheaf.RepresentationTheory.CoinducedHomotopyContinuous
import Sheaf.RepresentationTheory.CoinducedDiscreteEmbedding

/-!
# The coinduced contraction satisfies the homotopy identity

Source: Stacks Project, etale-cohomology.tex, Tag 0DVG,
label section-continuous-group-cohomology, final profinite comparison
(blueprint: lem-exc-coinduced-homotopy-identity).
-/

@[expose] public section

universe u v w

namespace Rep

/-- The inhomogeneous continuous cochain differential and the evaluation contraction
satisfy the contracting homotopy identity in every positive degree.
The witnesses `d` and `h` are uniquely specified by their pointwise formulas;
`h n` is the paper's `h_{n+1}`, so `n = 0` includes the degree-one identity.
Nested locally constant maps give the discrete topology on the coinduced module.
`Fin.contractNth` combines adjacent entries, or drops the last entry at the last index.
Integer scalar multiplication expresses alternating signs over an arbitrary ring.

Source: Stacks Project, etale-cohomology.tex, Tag 0DVG, label
section-continuous-group-cohomology (blueprint: lem-exc-coinduced-homotopy-identity).

Proof: (1) Use `lem-exc-coinduced-homotopy-continuous`
(`Rep.exists_coinduced_continuous_contraction`) for the evaluation contractions.
The displayed differential is continuous: right translation acts continuously on
this discrete coinduced module by `lem-exc-coinduced-discrete-embedding`
(`Rep.exists_coinduced_discrete_embedding`), and multiplication and deletion of tuple
entries are continuous. All operations are linear pointwise. Fix a positive degree,
a group tuple and `x`. Expand `d h` using right translation. Its leading term is
`F(x*g_1,g_2,...)(1)`, followed by the alternating interior product terms and the
endpoint with sign `(-1)^degree`. This also covers `d^0` in degree one.
(2) Expand `h d` by evaluating `d F` on `(x,g_1,...)` at one. Its leading term is
`F(g_1,...)(x)`, followed by the negative leading term from (1), the opposite interior
product terms, and the endpoint with sign `(-1)^(degree+1)`.
(3) Add the expansions. Each product term and endpoint cancels, leaving only
`F(g_1,...)(x)`. Extensionality in `x` and the tuple gives equality of continuous
cochains, namely `d^{degree-1} h_degree F + h_{degree+1} d^degree F = F`. -/
theorem coinduced_homotopy_identity
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A]
    (M : DiscreteContinuousRep.{v, u, w} A G) :
    ∃ (d : ∀ n : ℕ,
        LocallyConstant (Fin n → G) (LocallyConstant G M.obj.V) →ₗ[A]
          LocallyConstant (Fin (n + 1) → G) (LocallyConstant G M.obj.V))
      (h : ∀ n : ℕ,
        LocallyConstant (Fin (n + 1) → G) (LocallyConstant G M.obj.V) →ₗ[A]
          LocallyConstant (Fin n → G) (LocallyConstant G M.obj.V)),
      (∀ (n : ℕ) (F : LocallyConstant (Fin n → G) (LocallyConstant G M.obj.V))
        (g : Fin (n + 1) → G) (x : G),
        d n F g x = F (fun i ↦ g i.succ) (x * g 0) +
          ∑ j : Fin (n + 1),
            (-1 : ℤ) ^ (j.val + 1) • F (Fin.contractNth j (· * ·) g) x) ∧
      (∀ (n : ℕ)
        (F : LocallyConstant (Fin (n + 1) → G) (LocallyConstant G M.obj.V))
        (g : Fin n → G) (x : G), h n F g x = F (Fin.cons x g) 1) ∧
      (∀ (n : ℕ)
        (F : LocallyConstant (Fin (n + 1) → G) (LocallyConstant G M.obj.V)),
        d n (h n F) + h (n + 1) (d (n + 1) F) = F) := by
  sorry

end Rep
