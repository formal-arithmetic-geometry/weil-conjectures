/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fin.Tuple.Basic
import Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Bounded finite-evaluation rectangle replacement

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
agent-formulated scalar tame-kernel expansion. An exact literature reference for
this auxiliary quantitative statement is WANTED
(blueprint: lem-sfb-bounded-finite-evaluation-rectangle-replacement).

The positive cochain degree is written `n + 1`, so the primitive has degree `n`.
The differential is displayed pointwise using `Fin.contractNth`, whose last face
omits the final entry. With trivial action its degree-zero formula is zero.
All evaluation formulas are chosen before the coefficient space is quantified.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped BigOperators

namespace ContinuousCohomology

/-- Fixed finite continuous evaluation formulas give a contraction modulo a residual
which vanishes whenever the homogeneous cocycle vanishes on the ordered rectangle.
The norm is the supremum norm of continuous maps on a compact domain. No completeness
or closedness of coefficient subspaces is assumed. Parameter formulas keep `s` fixed.

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
agent-formulated scalar tame-kernel expansion; exact literature reference WANTED
(blueprint: lem-sfb-bounded-finite-evaluation-rectangle-replacement).

Proof:
1. Apply lem-sfb-topological-homogeneous-cochain-coordinates with E = Q_l and trivial
   action. Its inverse Psi sends c to its homogeneous successive-ratio function F;
   Phi evaluates at cumulative products. They commute with the differentials,
   including degree zero. Normed spaces have the required continuous operations.
2. Choose a right-coset transversal D of H in G, including 1. Write x = rho(x)s(x).
   The cosets are clopen, hence rho is continuous, and rho(hx) = h rho(x).
3. Use the specified free integer bases of def-weil-pbc-free-module for the augmented
   tuple chains B_q(G), with B_{-1} the integers. Alternating deletion squares to zero
   by pairing the two orders of deletion. Extend F to an additive map on B_degree(G).
4. Apply lem-sfb-ordered-join-partial-contraction to the degree+1 labeled sets H a_i,
   with anchors h a_i. Its S^h contracts through degree degree-1, is natural under
   translation, and has a fixed finite integral insertion/replacement expansion.
   Erasing colors gives a chain map e; its top-degree tuples lie in the rectangle.
5. Set P_{-1}=1, P_0[x]=[(0,rho(x)a_0)]. On basis tuples recursively set
   P_q(x)=S^{rho(x_0)}_{q-1}(P_{q-1}(boundary x)). The previous chain identity and
   boundary squared zero show the argument is a cycle; contraction gives boundary
   P_q=P_{q-1} boundary. Anchors are selected on basis tuples before linear extension.
6. Naturality and rho(hx)=h rho(x) give H-equivariance inductively. The finite expansion
   uses only vertices rho(x_j)a_i, with fixed coefficients and selections; keep repeated
   terms to avoid equality tests on values. Put A=eP, an augmented H-equivariant map.
7. Prefixing b defines C_b with boundary C_b+C_b boundary=1, including degree -1;
   translation gives h C_b=C_{hb} h.
8. Set Q_{-1}=0. On each basis tuple put Z_q=x-A_q x-Q_{q-1}(boundary x) and
   Q_q(x)=C_{x_0}Z_q. The augmentation of Z_0 is zero; inductively the previous
   homotopy identity and the chain identity give boundary Z_q=0. Thus
   1-A_q=boundary Q_q+Q_{q-1} boundary, including the bottom degree.
9. The same recursion proves H-equivariance of Q and fixed finite integral expansions
   with vertices x_j or rho(x_j)a_i. All these vertex maps are continuous.
10. Evaluate F on Q_{degree-1} and A_degree to obtain U F and W F. For a cocycle,
    F=delta(U F)+W F and delta(W F)=0. Every top-degree A tuple lies in the
    rectangle, so W F=0 if F vanishes there. These are actual cochain identities.
11. Average H-invariant functions by M L(x)=index(H)^{-1} sum_{s in D} L(sx).
    Writing sg=hu permutes right cosets and proves G-invariance without normality.
    Averaging commutes with deletion and fixes G-invariant F, so
    F=delta(M U F)+M W F, and M W F is a cocycle.
12. Conjugate by Phi and Psi: T=Phi M U Psi and R=Phi M W Psi. Expanding the
    finite chain formulas gives the stated continuous evaluation maps, independent
    of V, with coefficients integer multiples of index(H)^{-1}.
13. Integers have l-adic norm at most one, and the index has norm one since it is
    prime to l. The ultrametric inequality gives both supremum-norm bounds.
    Compactness bounds cochain norms. Finite linear sums preserve every linear
    coefficient subspace, including nonclosed ones, and require no limits in V.
14. On a profinite parameter family the same formulas precompose by (s,x)->(s,psi x)
    or (s,y)->(s,chi y); finite sums and fixed scalar multiplication are continuous.
    Apply the cochain identities to each slice. Empty parameter spaces are included.
    In degree one the primitive is a function on G^0, and its differential is zero;
    the augmented homotopy calculation above still gives the stated identity.
-/
theorem exists_boundedFiniteEvaluationRectangleReplacement
    (l : ℕ) [Fact l.Prime]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (H : OpenSubgroup G) (hindex : Nat.Coprime H.toSubgroup.index l)
    (n : ℕ) (a : Fin (n + 2) → G) :
    ∃ (t r : ℕ) (α : Fin t → ℚ_[l]) (β : Fin r → ℚ_[l])
      (ψ : Fin t → C(Fin n → G, Fin (n + 1) → G))
      (χ : Fin r → C(Fin (n + 1) → G, Fin (n + 1) → G)),
      (∀ j, ‖α j‖ ≤ 1) ∧ (∀ j, ‖β j‖ ≤ 1) ∧
      ∀ (V : Type v) [NormedAddCommGroup V] [NormedSpace ℚ_[l] V],
        (∀ x y : V, ‖x + y‖ ≤ max ‖x‖ ‖y‖) →
        ∃ (T : C(Fin (n + 1) → G, V) →ₗ[ℚ_[l]] C(Fin n → G, V))
          (R : C(Fin (n + 1) → G, V) →ₗ[ℚ_[l]] C(Fin (n + 1) → G, V)),
          (∀ (c : C(Fin (n + 1) → G, V)) (x : Fin n → G),
            T c x = ∑ j : Fin t, α j • c (ψ j x)) ∧
          (∀ (c : C(Fin (n + 1) → G, V)) (y : Fin (n + 1) → G),
            R c y = ∑ j : Fin r, β j • c (χ j y)) ∧
          (∀ c : C(Fin (n + 1) → G, V),
            (∀ g : Fin (n + 2) → G,
              c (fun i ↦ g i.succ) + ∑ j : Fin (n + 2),
                (-1 : ℚ_[l]) ^ (j.val + 1) • c (Fin.contractNth j (· * ·) g) = 0) →
            (∀ g : Fin (n + 2) → G,
              R c (fun i ↦ g i.succ) + ∑ j : Fin (n + 2),
                (-1 : ℚ_[l]) ^ (j.val + 1) • R c (Fin.contractNth j (· * ·) g) = 0) ∧
            (∀ g : Fin (n + 1) → G,
              c g = T c (fun i ↦ g i.succ) +
                (∑ j : Fin (n + 1),
                  (-1 : ℚ_[l]) ^ (j.val + 1) • T c (Fin.contractNth j (· * ·) g)) + R c g) ∧
            ((∀ x : Fin (n + 2) → H,
              c (fun i ↦ ((x i.castSucc : G) * a i.castSucc)⁻¹ *
                ((x i.succ : G) * a i.succ)) = 0) → R c = 0)) ∧
          (∀ c : C(Fin (n + 1) → G, V), ‖T c‖ ≤ ‖c‖ ∧ ‖R c‖ ≤ ‖c‖) ∧
          (∀ (W : Submodule ℚ_[l] V) (c : C(Fin (n + 1) → G, V)),
            (∀ x, c x ∈ W) → (∀ x, T c x ∈ W) ∧ (∀ y, R c y ∈ W)) ∧
          ∀ (S : Profinite.{w}) (c : C(S × (Fin (n + 1) → G), V)),
            Continuous (fun p : S × (Fin n → G) ↦
              ∑ j : Fin t, α j • c (p.1, ψ j p.2)) ∧
            Continuous (fun p : S × (Fin (n + 1) → G) ↦
              ∑ j : Fin r, β j • c (p.1, χ j p.2)) := by
  sorry

end ContinuousCohomology
