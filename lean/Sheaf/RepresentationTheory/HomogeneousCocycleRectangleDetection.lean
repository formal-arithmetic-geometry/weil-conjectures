/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Defs.Induced
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Rectangular detection of continuous homogeneous cocycles

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
agent arithmetic expansion: comparison with the ordered join of subgroup torsors.
The chain calculation is not in the blueprint; a continuous-coefficient reference
is WANTED (blueprint: lem-sfb-homogeneous-cocycle-rectangle-detection).

The finite-product cochains and their alternating deletion differentials are
written pointwise. No completion or closure of coboundaries occurs.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped BigOperators

namespace Representation

/-- A continuous homogeneous positive-degree cocycle vanishing on an ordered
rectangle of right translates of an open subgroup is a continuous coboundary
on that subgroup. The topology of `H` is induced from `G`. The field operations
are continuous except that continuity of field inversion is not required.
The representation `ρ` is linear and its evaluation action is jointly continuous.
The map `i.succAbove` omits the coordinate `i` without changing the other positions.

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
agent arithmetic expansion below local continuous-cocycle descent. This argument
is not in the blueprint; a continuous-coefficient partial-resolution reference
is WANTED (blueprint: lem-sfb-homogeneous-cocycle-rectangle-detection).

Proof:
1. Let B_q(Y) be the free abelian group on ordered (q+1)-tuples, including
   repeated entries, and B_{-1}(Y) the integers on the empty tuple
   [def-weil-pbc-free-module]. The alternating deletion boundary, augmented
   by d[y]=1, has square zero by pairing the two orders of deleting positions.
   Extend f additively to F on B_n(G). The cocycle identity gives Fd=0;
   diagonal equivariance gives F(gz)=rho(g)F(z).
2. Use lem-sfb-ordered-join-partial-contraction for the n+1 separately labeled
   torsors X_i=H a_i. Erasing labels is a chain map e from ordered join chains J
   to B(G). Every degree-n symbol has colors 0,...,n in that order, so Fe=0
   there by the rectangle hypothesis. Anchors v_i(h)=h a_i give contractions
   S^h satisfying dS^h+S^h d=1 through degree n-1, including the augmentation.
3. Set P_{-1}=1 and P_0[h]=[(0,h a_0)]. Inductively, for x=[h_0,...,h_q],
   set P_q(x)=S^{h_0}(P_{q-1}(dx)) and extend additively. The previous chain
   identity and d squared zero show that P_{q-1}(dx) is a cycle. The cited
   contraction, used only in degree q-1 at most n-1, gives dP_q=P_{q-1}d.
4. Left multiplication carries the anchors at h to those at gh. Naturality
   of the cited contraction proves equivariance of P. Its finite-formula
   clause inductively expresses each P_q tuple as a fixed finite integer
   combination of symbols with vertices h_j a_i. Coefficients, colors and
   coordinate choices do not depend on the input values.
5. Write I for coordinatewise inclusion B(H) to B(G), and A=eP. These are
   equivariant augmented chain maps through degree n, identical in degree -1.
   Prefixing b defines C_b, also C_b(1)=[b]. Alternating deletion directly
   gives dC_b+C_b d=1 and gC_b(z)=C_{gb}(gz).
6. Put Q_{-1}=0. On x=[h_0,...,h_q] define
   Z_q(x)=I_q(x)-A_q(x)-Q_{q-1}(dx) and Q_q(x)=C_{h_0}(Z_q(x)), then extend
   additively. The augmentation of Z_0 is zero. Inductively the previous
   homotopy identity and the chain-map identities give dZ_q=0. The prefix
   identity yields I_q-A_q=dQ_q+Q_{q-1}d, including degree zero.
7. The same recursion and the prefix identity prove equivariance of Q.
   Deletion, subtraction and prefixing preserve the finite-formula property:
   each Q_q tuple is a fixed finite integer sum of tuples with entries h_j
   or h_j a_i. No choices or equality tests depend on the input.
8. Define t(h_0,...,h_{n-1})=F(Q_{n-1}[h_0,...,h_{n-1}]); n is positive.
   Its formula is a finite sum of integer multiples of f evaluated at tuples
   of coordinate inclusions or right translates. The induced inclusion H to G
   is continuous [def-kun-subspace-topology], as are these coordinate maps,
   right translations, f, finite sums and negation. Hence t is continuous.
9. Equivariance of F and Q gives diagonal H-equivariance of t. Apply F to
   I_n-A_n=dQ_n+Q_{n-1}d. Since FA_n=FeP_n=0 and Fd=0, the result is exactly
   f restricted to H = delta t. All sums are finite integer sums, so this
   applies in every characteristic without completeness or closed boundaries.
-/
theorem homogeneous_cocycle_rectangle_detection
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : Type w) [AddCommGroup M] [Module K M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul K M]
    (ρ : G →* (M ≃ₗ[K] M)) (hρ : Continuous (fun p : G × M ↦ ρ p.1 p.2))
    (n : ℕ) (hn : 1 ≤ n) (H : OpenSubgroup G) (a : Fin (n + 1) → G)
    (f : C(Fin (n + 1) → G, M))
    (hequiv : ∀ (g : G) (x : Fin (n + 1) → G),
      f (fun i ↦ g * x i) = ρ g (f x))
    (hcocycle : ∀ x : Fin (n + 2) → G,
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • f (fun j ↦ x (i.succAbove j)) = 0)
    (hrectangle : ∀ x : Fin (n + 1) → H,
      f (fun i ↦ (x i : G) * a i) = 0) :
    ∃ t : C(Fin n → H, M),
      (∀ (g : H) (x : Fin n → H), t (fun i ↦ g * x i) = ρ (g : G) (t x)) ∧
      ∀ x : Fin (n + 1) → H,
        f (fun i ↦ (x i : G)) =
          ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • t (fun j ↦ x (i.succAbove j)) := by
  sorry

end Representation
