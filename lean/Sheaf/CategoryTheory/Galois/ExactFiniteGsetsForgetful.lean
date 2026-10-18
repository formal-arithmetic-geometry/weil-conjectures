/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.Topology.Category.FinTopCat
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.CofilteredSystem

/-!
# Exact finite-valued functors on finite continuous group sets

Source: Stacks Project, Fundamental Groups of Schemes, Tag 0BMV,
`pione-lemma-second-fundamental-functor`
(blueprint: lem-wf-exact-finite-gsets-forgetful).
-/

@[expose] public section

universe g u

open CategoryTheory CategoryTheory.Limits
open scoped FintypeCatDiscrete

namespace ContAction

/-- An exact finite-valued functor on finite continuous `G`-sets is naturally isomorphic
 to the underlying-set functor. Source: Stacks Project, Tag 0BMV,
 `pione-lemma-second-fundamental-functor`
 (blueprint: lem-wf-exact-finite-gsets-forgetful).

Proof, following Tag 0BMV and the expanded DAG proof:
1. Empty and singleton sets, finite coproducts and products, invariant equalizers,
   pullbacks, and invariant equivalence-relation quotients give the usual finite
   limits and colimits of continuous finite actions. Product stabilizers are finite
   intersections of open stabilizers; subsets retain stabilizers; quotient stabilizers
   contain open stabilizers. Thus these discrete actions remain continuous. Exactness
   (`def-galois-exact-functor`) preserves these constructions and their universal maps.
2. For nonempty X, the pushout of the two maps X to a singleton is a singleton.
   Were H(X) empty, the image pushout would have two points. Hence H(X) is nonempty.
3. An equivariant surjection q is the coequalizer of its kernel-pair projections.
   Exactness makes H(q) surjective and identifies the image kernel pair with the
   kernel pair of H(q), also for the empty surjection.
4. For an open normal finite-index subgroup N, write Q_N = G/N. Its square is the
   disjoint union of |Q_N| copies of Q_N, by (gN, gaN) in the aN-summand.
   Exactness gives |H(Q_N)| squared = |Q_N| times |H(Q_N)|; positivity from step 2
   permits cancellation, so |H(Q_N)| = |Q_N|.
5. Open normal finite-index subgroups, with arrows M to N for M contained in N,
   form a small cofiltered category: it contains G and is closed under intersection.
   Its finite nonempty H(Q_N) have a compatible family gamma_N by
   `lem-trf-cofiltered-finite-sets-section`, the Mathlib theorem
   `nonempty_sections_of_finite_cofiltered_system`. This index is a set of subgroups,
   rather than the potentially large category of all finite actions.
6. The action kernel K_X is open, normal and finite-index: it is the finite
   intersection of point stabilizers and G/K_X embeds into the finite permutation
   group of X. For N contained in K_X and x in X, let f_{N,x}(gN) = gx and set
   t_X(x) = H(f_{N,x})(gamma_N). Intersecting two choices of N and compatibility
   of gamma show independence. Equivariance of a : X to Y gives naturality after
   refining to a subgroup contained in both kernels. For empty X use the empty map.
7. On Q_N, t sends aN to H(R_a)(gamma_N). Distinct right translations have empty
   equalizer, which H preserves. Thus these values are distinct; step 4 gives
   bijectivity of t on Q_N.
8. Finite coproduct preservation makes t bijective on finite coproducts of Q_N,
   including the empty coproduct. Cover X by Y, the coproduct indexed by x in X
   of Q_{K_X}, using f_{K_X,x}. Both q : Y to X and H(q) are surjective, so
   naturality and bijectivity on Y make t_X surjective.
9. For t_X(x) = t_X(x'), choose y,y' above x,x' in Y. The preserved kernel pair
   R = Y times_X Y supplies an element of H(R) with coordinates t_Y(y),t_Y(y').
   Surjectivity of t_R lifts it to R. Naturality and injectivity of t_Y identify
   its coordinates with y,y', giving x = x'. Hence every t_X is bijective.
   The inverse functions are natural by the naturality equation for t, so t is
   the asserted natural isomorphism. -/
theorem nonempty_forget_iso_of_exact_finite {G : Type g} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ContAction FintypeCat.{u} G ⥤ Type u)
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [∀ X : ContAction FintypeCat.{u} G, Finite (H.obj X)] :
    Nonempty ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙ FintypeCat.incl) ≅ H) := by
  sorry

end ContAction
