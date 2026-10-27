/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Sheaf.GroupTheory.OpenOrbitFunctor
public import Sheaf.CategoryTheory.Galois.AutProfinite
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic
public import Mathlib.GroupTheory.GroupAction.Defs

/-! # Finite orbit-coordinate realizers form a two-sided Cauchy net

Source: Bhatt--Scholze, Proposition 7.1.5, printed p. 64, finite-intersection and
Cauchy coset-filter argument in finite-coordinate net form.
(blueprint: lem-sfb-orbit-automorphism-cauchy-realizers)
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory Topology
open scoped Pointwise

namespace TopologicalGroup

/-- A natural automorphism of the open-orbit forgetful functor has simultaneous finite
coordinate realizers. The prescribed-value sets are nonempty closed stabilizer cosets,
with the finite intersection property including the empty intersection. Including both
an identity coset and its inverse-image coordinate forces both ordered differences into
the corresponding open subgroup, hence gives the two-sided Cauchy condition.

Source: Bhatt--Scholze, Proposition 7.1.5, printed p. 64.
(blueprint: lem-sfb-orbit-automorphism-cauchy-realizers)

Proof:
1. For each finite tagged set, write its coordinates as a_x U_x. Intersect their open
   conjugate stabilizers a_x U_x a_x inverse, using G for the empty intersection. The
   maps hV -> hx are well-defined equivariant arrows of the open-orbit category
   (`def-sfb-open-orbit-functor`).
2. Naturality along these maps shows that a representative of alpha_V(V) realizes every
   coordinate. Choose such a representative for every finite set, including the empty set
   (where 1 is a possible choice).
3. A coordinate's realizer set is a left coset of its stabilizer. An open subgroup is
   closed because its complement is a union of open cosets. Thus these sets are nonempty
   and closed. The chosen realizer lies in each finite intersection; the empty one is G.
4. Put y = alpha_U inverse(U). If a and b realize both U and y, then aU = bU gives
   a inverse * b in U. Also ay = by = U gives y = b inverse U and hence a * b inverse
   in U. This uses left cosets and does not require normality.
5. Given an identity neighborhood W, choose an open subgroup U contained in W. The
   finite set consisting of the tagged U and y is a threshold: all larger indices have
   both differences in U and thus in W. Coincident coordinates give a singleton.
-/
theorem orbitAutomorphismCauchyRealizers
    (G : Type u) [Group G] [TopologicalSpace G] [T2Space G] [NonarchimedeanGroup G]
    (α : Aut (openOrbitForget G)) :
    ∃ g : Finset (Σ U : OpenSubgroup G, G ⧸ U.toSubgroup) → G,
      (∀ (F : Finset (Σ U : OpenSubgroup G, G ⧸ U.toSubgroup))
          (x : Σ U : OpenSubgroup G, G ⧸ U.toSubgroup), x ∈ F →
        g F • x.2 = α.hom.app x.1 x.2) ∧
      (∀ x : Σ U : OpenSubgroup G, G ⧸ U.toSubgroup,
        {a : G | a • x.2 = α.hom.app x.1 x.2}.Nonempty ∧
        IsClosed {a : G | a • x.2 = α.hom.app x.1 x.2} ∧
        ∃ r : G, {a : G | a • x.2 = α.hom.app x.1 x.2} =
          r • (MulAction.stabilizer G x.2 : Set G)) ∧
      (∀ F : Finset (Σ U : OpenSubgroup G, G ⧸ U.toSubgroup),
        (⋂ x ∈ F, {a : G | a • x.2 = α.hom.app x.1 x.2}).Nonempty) ∧
      (⋂ x ∈ (∅ : Finset (Σ U : OpenSubgroup G, G ⧸ U.toSubgroup)),
        {a : G | a • x.2 = α.hom.app x.1 x.2}) = Set.univ ∧
      (∀ (U : OpenSubgroup G)
          (F F' : Finset (Σ V : OpenSubgroup G, G ⧸ V.toSubgroup)),
        (⟨U, QuotientGroup.mk (1 : G)⟩ : Σ V : OpenSubgroup G, G ⧸ V.toSubgroup) ∈ F →
        (⟨U, α.inv.app U (QuotientGroup.mk (1 : G))⟩ :
          Σ V : OpenSubgroup G, G ⧸ V.toSubgroup) ∈ F →
        (⟨U, QuotientGroup.mk (1 : G)⟩ : Σ V : OpenSubgroup G, G ⧸ V.toSubgroup) ∈ F' →
        (⟨U, α.inv.app U (QuotientGroup.mk (1 : G))⟩ :
          Σ V : OpenSubgroup G, G ⧸ V.toSubgroup) ∈ F' →
        (g F)⁻¹ * g F' ∈ U ∧ g F * (g F')⁻¹ ∈ U) ∧
      (∀ W ∈ 𝓝 (1 : G),
        ∃ F₀ : Finset (Σ U : OpenSubgroup G, G ⧸ U.toSubgroup),
          ∀ (F F' : Finset (Σ U : OpenSubgroup G, G ⧸ U.toSubgroup)),
            F₀ ⊆ F → F₀ ⊆ F' → (g F)⁻¹ * g F' ∈ W ∧ g F * (g F')⁻¹ ∈ W) := by
  sorry

end TopologicalGroup
