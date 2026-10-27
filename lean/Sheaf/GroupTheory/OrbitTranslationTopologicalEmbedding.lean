/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.GroupTheory.OpenOrbitFunctor
public import Sheaf.CategoryTheory.Galois.AutProfinite
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-! # Translation into automorphisms of the open-orbit functor

Source: Bhatt--Scholze, Proposition 7.1.5, printed pp. 63--64.
(blueprint: lem-sfb-orbit-translation-topological-embedding)
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory Topology

namespace TopologicalGroup

/-- Translation embeds a Hausdorff group with an open-subgroup identity basis into the
pointwise topological group of natural automorphisms of its open-orbit forgetful functor.
The first clauses record smallness in the universe of the group. The next characterizes
natural automorphisms as precisely the bijective families commuting with every orbit arrow.
The homomorphism is specified by its translation formula, without any choice of action.
The remaining clauses identify conjugate stabilizers, clopen left-coset fibres, and the
inverse image of the identity-coset fixing condition.

Source: Bhatt--Scholze, Proposition 7.1.5, printed pp. 63--64.
(blueprint: lem-sfb-orbit-translation-topological-embedding)

Proof:
1. Open subgroups are a set and equivariant maps are a subset of the functions between
   coset sets. The induced category has their usual identities and composition
   (`def-sfb-open-orbit-functor`).
2. A natural automorphism is a family of bijections commuting with all equivariant maps.
   Conversely this commutation also holds for the inverse bijections, giving a natural
   inverse. Components determine the natural automorphism uniquely.
3. Translation by g has inverse translation by g inverse; equivariance gives naturality.
   The action identities give the identity and multiplication laws for the homomorphism.
4. To control the product at (alpha,beta) on (U,x), prescribe beta'(x)=beta(x) and
   alpha'(beta(x))=alpha(beta(x)). Finite intersections prove joint continuity using
   `def-sfb-set-functor-aut-pointwise-topology`.
5. To control inversion at alpha on x, prescribe alpha'(alpha inverse(x))=x.
   Bijectivity and finite intersections prove continuity of inversion.
6. For x=aU, hx=x is equivalent to a inverse * h * a belonging to U. Thus the stabilizer
   is aUa inverse. Conjugation and left translation are homeomorphisms, so this subgroup
   and its left cosets are open. Their complements are unions of other cosets, hence
   they are closed. If y=bU, g0=b*a inverse sends x to y; the fibre is g0*Stab(x).
7. Coordinate conditions pull back to these clopen fibres, proving continuity. At U,
   gU=U is exactly g belonging to U, giving the asserted preimage formula.
8. If g differs from h, Hausdorffness gives a neighbourhood of 1 omitting h inverse*g.
   Choose an open subgroup inside it. Evaluation on its identity coset distinguishes
   the two translations, proving injectivity.
9. The condition alpha_U(U)=gU pulls back to gU. These translates are a basis of G,
   so the induced topology contains its original topology. Continuity gives the reverse
   containment, proving the topological embedding.
-/
theorem orbitTranslation_topologicalEmbedding
    (G : Type u) [Group G] [TopologicalSpace G] [T2Space G] [NonarchimedeanGroup G] :
    Small.{u} (OpenOrbitCategory G) ∧
      (∀ U V : OpenOrbitCategory G, Small.{u} (U ⟶ V)) ∧
      (∀ a : ∀ U : OpenOrbitCategory G, (G ⧸ U.toSubgroup) → G ⧸ U.toSubgroup,
        ((∀ U : OpenOrbitCategory G, Function.Bijective (a U)) ∧
          (∀ (U V : OpenOrbitCategory G) (f : U ⟶ V) (x : G ⧸ U.toSubgroup),
            (openOrbitForget G).map f (a U x) = a V ((openOrbitForget G).map f x))) ↔
          ∃! α : Aut (openOrbitForget G),
            ∀ (U : OpenOrbitCategory G) (x : G ⧸ U.toSubgroup), α.hom.app U x = a U x) ∧
      ∃ Φ : G →* Aut (openOrbitForget G),
        (∀ (g : G) (U : OpenOrbitCategory G) (x : G ⧸ U.toSubgroup),
          (Φ g).hom.app U x = g • x) ∧
        IsTopologicalGroup (Aut (openOrbitForget G)) ∧
        IsEmbedding Φ ∧
        (∀ (U : OpenOrbitCategory G) (a : G),
          (MulAction.stabilizer G (QuotientGroup.mk a : G ⧸ U.toSubgroup) : Set G) =
            (fun h : G ↦ a * h * a⁻¹) '' (U.toSubgroup : Set G)) ∧
        (∀ (U : OpenOrbitCategory G) (a : G) (y : G ⧸ U.toSubgroup),
          ∃ g₀ : G,
            g₀ • (QuotientGroup.mk a : G ⧸ U.toSubgroup) = y ∧
            {g : G | g • (QuotientGroup.mk a : G ⧸ U.toSubgroup) = y} =
              (fun h : G ↦ g₀ * h) ''
                (MulAction.stabilizer G (QuotientGroup.mk a : G ⧸ U.toSubgroup) : Set G) ∧
            IsClopen {g : G | g • (QuotientGroup.mk a : G ⧸ U.toSubgroup) = y}) ∧
        (∀ U : OpenOrbitCategory G,
          Φ ⁻¹' {α : Aut (openOrbitForget G) |
            α.hom.app U (QuotientGroup.mk 1 : G ⧸ U.toSubgroup) =
              (QuotientGroup.mk 1 : G ⧸ U.toSubgroup)} = (U.toSubgroup : Set G)) := by
  sorry

end TopologicalGroup
